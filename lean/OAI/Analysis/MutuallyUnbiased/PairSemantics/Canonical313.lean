import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes52

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw10016 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![-2, -1, 3]]

def raw10016step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

theorem canonical10016 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10016 = injectiveMoment H node1890 := by
  calc
    injectiveMoment H raw10016 = injectiveMoment H raw10016step0 := by
      have heq : raw10016step0 = (fun i j => raw10016 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10016 permutation308 permutation3
    _ = injectiveMoment H node1890 := by rfl

def raw10017 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![-2, -2, 4]]

def raw10017step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]

theorem canonical10017 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10017 = injectiveMoment H node1541 := by
  calc
    injectiveMoment H raw10017 = injectiveMoment H raw10017step0 := by
      have heq : raw10017step0 = (fun i j => raw10017 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10017 permutation308 permutation3
    _ = injectiveMoment H node1541 := by rfl

def raw10018 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1], ![-3, 0, 3]]

def raw10018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]

theorem canonical10018 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10018 = injectiveMoment H node1409 := by
  calc
    injectiveMoment H raw10018 = injectiveMoment H raw10018step0 := by
      have heq : raw10018step0 = (fun i j => raw10018 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10018 permutation308 permutation3
    _ = injectiveMoment H node1409 := by rfl

def raw10019 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2], ![-3, -1, 4]]

def raw10019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]

theorem canonical10019 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10019 = injectiveMoment H node1386 := by
  calc
    injectiveMoment H raw10019 = injectiveMoment H raw10019step0 := by
      have heq : raw10019step0 = (fun i j => raw10019 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10019 permutation308 permutation3
    _ = injectiveMoment H node1386 := by rfl

def raw10020 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3]]

def raw10020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![-1, -2, 3]]

def raw10020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]

theorem canonical10020 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10020 = injectiveMoment H node884 := by
  calc
    injectiveMoment H raw10020 = injectiveMoment H raw10020step0 := by
      have hz : ∀ j, raw10020 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw10020step0 = (fun i j => raw10020 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw10020 permutation258 hz
    injectiveMoment H raw10020step0 = injectiveMoment H raw10020step1 := by
      have heq : raw10020step1 = (fun i j => raw10020step0 (permutation128 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10020step0 permutation128 permutation3
    _ = injectiveMoment H node884 := by rfl

def raw10021 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]

def raw10021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]

theorem canonical10021 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10021 = injectiveMoment H node1891 := by
  calc
    injectiveMoment H raw10021 = injectiveMoment H raw10021step0 := by
      have heq : raw10021step0 = (fun i j => raw10021 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10021 permutation308 permutation3
    _ = injectiveMoment H node1891 := by rfl

def raw10022 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![-2, -2, 4]]

def raw10022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical10022 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10022 = injectiveMoment H node1542 := by
  calc
    injectiveMoment H raw10022 = injectiveMoment H raw10022step0 := by
      have heq : raw10022step0 = (fun i j => raw10022 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10022 permutation308 permutation3
    _ = injectiveMoment H node1542 := by rfl

def raw10023 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![-2, -3, 5]]

def raw10023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]

theorem canonical10023 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10023 = injectiveMoment H node1437 := by
  calc
    injectiveMoment H raw10023 = injectiveMoment H raw10023step0 := by
      have heq : raw10023step0 = (fun i j => raw10023 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10023 permutation308 permutation3
    _ = injectiveMoment H node1437 := by rfl

def raw10024 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]

def raw10024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]

theorem canonical10024 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10024 = injectiveMoment H node1410 := by
  calc
    injectiveMoment H raw10024 = injectiveMoment H raw10024step0 := by
      have heq : raw10024step0 = (fun i j => raw10024 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10024 permutation308 permutation3
    _ = injectiveMoment H node1410 := by rfl

def raw10025 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![-3, -1, 4]]

def raw10025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]

theorem canonical10025 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10025 = injectiveMoment H node1387 := by
  calc
    injectiveMoment H raw10025 = injectiveMoment H raw10025step0 := by
      have heq : raw10025step0 = (fun i j => raw10025 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10025 permutation308 permutation3
    _ = injectiveMoment H node1387 := by rfl

def raw10026 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![-3, -2, 5]]

def raw10026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]

theorem canonical10026 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10026 = injectiveMoment H node1379 := by
  calc
    injectiveMoment H raw10026 = injectiveMoment H raw10026step0 := by
      have heq : raw10026step0 = (fun i j => raw10026 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10026 permutation308 permutation3
    _ = injectiveMoment H node1379 := by rfl

def raw10027 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![-2, -2, 4]]

def raw10027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical10027 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10027 = injectiveMoment H node1542 := by
  calc
    injectiveMoment H raw10027 = injectiveMoment H raw10027step0 := by
      have heq : raw10027step0 = (fun i j => raw10027 (permutation309 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10027 permutation309 permutation3
    _ = injectiveMoment H node1542 := by rfl

def raw10028 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -3, 5]]

def raw10028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical10028 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10028 = injectiveMoment H node1438 := by
  calc
    injectiveMoment H raw10028 = injectiveMoment H raw10028step0 := by
      have heq : raw10028step0 = (fun i j => raw10028 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10028 permutation308 permutation3
    _ = injectiveMoment H node1438 := by rfl

def raw10029 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1], ![-3, 0, 3]]

def raw10029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]

theorem canonical10029 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10029 = injectiveMoment H node1411 := by
  calc
    injectiveMoment H raw10029 = injectiveMoment H raw10029step0 := by
      have heq : raw10029step0 = (fun i j => raw10029 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10029 permutation308 permutation3
    _ = injectiveMoment H node1411 := by rfl

def raw10030 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![-3, -1, 4]]

def raw10030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]

theorem canonical10030 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10030 = injectiveMoment H node1388 := by
  calc
    injectiveMoment H raw10030 = injectiveMoment H raw10030step0 := by
      have heq : raw10030step0 = (fun i j => raw10030 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10030 permutation308 permutation3
    _ = injectiveMoment H node1388 := by rfl

def raw10031 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![-3, -1, 4]]

def raw10031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]

theorem canonical10031 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10031 = injectiveMoment H node1389 := by
  calc
    injectiveMoment H raw10031 = injectiveMoment H raw10031step0 := by
      have heq : raw10031step0 = (fun i j => raw10031 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10031 permutation308 permutation3
    _ = injectiveMoment H node1389 := by rfl

def raw10032 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![-3, -1, 4]]

def raw10032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]

theorem canonical10032 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10032 = injectiveMoment H node1390 := by
  calc
    injectiveMoment H raw10032 = injectiveMoment H raw10032step0 := by
      have heq : raw10032step0 = (fun i j => raw10032 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10032 permutation308 permutation3
    _ = injectiveMoment H node1390 := by rfl

def raw10033 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-3, -1, 4]]

def raw10033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -3, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical10033 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10033 = injectiveMoment H node2380 := by
  calc
    injectiveMoment H raw10033 = injectiveMoment H raw10033step0 := by
      have heq : raw10033step0 = (fun i j => raw10033 (permutation366 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10033 permutation366 permutation5
    _ = injectiveMoment H node2380 := by rfl

def raw10034 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![-3, -2, 5]]

def raw10034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]

theorem canonical10034 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10034 = injectiveMoment H node1381 := by
  calc
    injectiveMoment H raw10034 = injectiveMoment H raw10034step0 := by
      have heq : raw10034step0 = (fun i j => raw10034 (permutation308 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10034 permutation308 permutation3
    _ = injectiveMoment H node1381 := by rfl

def raw10035 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-2, -1, 3]]

def raw10035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]

theorem canonical10035 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10035 = injectiveMoment H node1868 := by
  calc
    injectiveMoment H raw10035 = injectiveMoment H raw10035step0 := by
      have heq : raw10035step0 = (fun i j => raw10035 (permutation395 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10035 permutation395 permutation3
    _ = injectiveMoment H node1868 := by rfl

def raw10036 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-2, -1, 3]]

def raw10036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]

def raw10036step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical10036 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10036 = injectiveMoment H node1434 := by
  calc
    injectiveMoment H raw10036 = injectiveMoment H raw10036step0 := by
      have heq : raw10036step0 = -raw10036 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10036).symm
    injectiveMoment H raw10036step0 = injectiveMoment H raw10036step1 := by
      have heq : raw10036step1 = (fun i j => raw10036step0 (permutation341 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10036step0 permutation341 permutation8
    _ = injectiveMoment H node1434 := by rfl

def raw10037 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![-1, 2, -1], ![-2, -1, 3]]

def raw10037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]

def raw10037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical10037 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10037 = injectiveMoment H node1434 := by
  calc
    injectiveMoment H raw10037 = injectiveMoment H raw10037step0 := by
      have heq : raw10037step0 = -raw10037 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10037).symm
    injectiveMoment H raw10037step0 = injectiveMoment H raw10037step1 := by
      have heq : raw10037step1 = (fun i j => raw10037step0 (permutation347 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10037step0 permutation347 permutation8
    _ = injectiveMoment H node1434 := by rfl

def raw10038 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-2, -1, 3]]

def raw10038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -2, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]

theorem canonical10038 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10038 = injectiveMoment H node2469 := by
  calc
    injectiveMoment H raw10038 = injectiveMoment H raw10038step0 := by
      have heq : raw10038step0 = (fun i j => raw10038 (permutation340 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10038 permutation340 permutation5
    _ = injectiveMoment H node2469 := by rfl

def raw10039 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-2, -2, 4]]

def raw10039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]

theorem canonical10039 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10039 = injectiveMoment H node1530 := by
  calc
    injectiveMoment H raw10039 = injectiveMoment H raw10039step0 := by
      have heq : raw10039step0 = (fun i j => raw10039 (permutation339 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10039 permutation339 permutation5
    _ = injectiveMoment H node1530 := by rfl

def raw10040 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-2, 0, -1, 3], ![0, -1, 3, -2]]

def raw10040step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical10040 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10040 = injectiveMoment H node3128 := by
  calc
    injectiveMoment H raw10040 = injectiveMoment H raw10040step0 := by
      have heq : raw10040step0 = (fun i j => raw10040 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10040 permutation294 permutation9
    _ = injectiveMoment H node3128 := by rfl

def raw10041 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 0, 3, -2]]

def raw10041step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical10041 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10041 = injectiveMoment H node3362 := by
  calc
    injectiveMoment H raw10041 = injectiveMoment H raw10041step0 := by
      have heq : raw10041step0 = (fun i j => raw10041 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10041 permutation294 permutation9
    _ = injectiveMoment H node3362 := by rfl

def raw10042 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def raw10042step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, -1, 1, 0], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1], ![1, 0, 1, -2], ![1, 1, -3, 1]]

def raw10042step1 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 1, -3]]

theorem canonical10042 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw10042 = injectiveMoment H node3197 := by
  calc
    injectiveMoment H raw10042 = injectiveMoment H raw10042step0 := by
      have heq : raw10042step0 = -raw10042 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw10042).symm
    injectiveMoment H raw10042step0 = injectiveMoment H raw10042step1 := by
      have heq : raw10042step1 = (fun i j => raw10042step0 (permutation258 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10042step0 permutation258 permutation29
    _ = injectiveMoment H node3197 := by rfl

def raw10043 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-2, 0, -1, 3], ![0, -1, 3, -2]]

def raw10043step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical10043 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10043 = injectiveMoment H node3129 := by
  calc
    injectiveMoment H raw10043 = injectiveMoment H raw10043step0 := by
      have heq : raw10043step0 = (fun i j => raw10043 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10043 permutation294 permutation9
    _ = injectiveMoment H node3129 := by rfl

def raw10044 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, -1, -1, 3], ![-1, 0, 3, -2]]

def raw10044step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical10044 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10044 = injectiveMoment H node3363 := by
  calc
    injectiveMoment H raw10044 = injectiveMoment H raw10044step0 := by
      have heq : raw10044step0 = (fun i j => raw10044 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10044 permutation294 permutation9
    _ = injectiveMoment H node3363 := by rfl

def raw10045 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1], ![-1, 0, -1, 2], ![-1, -1, 3, -1]]

def raw10045step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical10045 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10045 = injectiveMoment H node3359 := by
  calc
    injectiveMoment H raw10045 = injectiveMoment H raw10045step0 := by
      have heq : raw10045step0 = (fun i j => raw10045 (permutation398 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10045 permutation398 permutation10
    _ = injectiveMoment H node3359 := by rfl

def raw10046 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-2, 0, -1, 3], ![0, -1, 3, -2]]

def raw10046step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical10046 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10046 = injectiveMoment H node3130 := by
  calc
    injectiveMoment H raw10046 = injectiveMoment H raw10046step0 := by
      have heq : raw10046step0 = (fun i j => raw10046 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10046 permutation294 permutation9
    _ = injectiveMoment H node3130 := by rfl

def raw10047 : Matrix (Fin 6) (Fin 4) ℤ := ![![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0], ![-1, -1, -1, 3], ![-1, 0, 3, -2]]

def raw10047step0 : Matrix (Fin 6) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical10047 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10047 = injectiveMoment H node3364 := by
  calc
    injectiveMoment H raw10047 = injectiveMoment H raw10047step0 := by
      have heq : raw10047step0 = (fun i j => raw10047 (permutation294 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10047 permutation294 permutation9
    _ = injectiveMoment H node3364 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
