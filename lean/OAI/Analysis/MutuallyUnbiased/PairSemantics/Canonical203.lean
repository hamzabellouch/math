import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw6496 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw6496step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6496 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6496 = injectiveMoment H node2598 := by
  calc
    injectiveMoment H raw6496 = injectiveMoment H raw6496step0 := by
      have heq : raw6496step0 = (fun i j => raw6496 (permutation40 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6496 permutation40 permutation15
    _ = injectiveMoment H node2598 := by rfl

def raw6497 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 0, 1, -1], ![0, 2, -3, 1], ![1, -1, 0, 0]]

def raw6497step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 0, 0]]

theorem canonical6497 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6497 = injectiveMoment H node2611 := by
  calc
    injectiveMoment H raw6497 = injectiveMoment H raw6497step0 := by
      have heq : raw6497step0 = (fun i j => raw6497 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6497 permutation39 permutation9
    _ = injectiveMoment H node2611 := by rfl

def raw6498 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical6498 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6498 = injectiveMoment H node1053 := by
  rfl

def raw6499 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, 0, 0, -1]]

def raw6499step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1]]

theorem canonical6499 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6499 = injectiveMoment H node2598 := by
  calc
    injectiveMoment H raw6499 = injectiveMoment H raw6499step0 := by
      have heq : raw6499step0 = (fun i j => raw6499 (permutation45 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6499 permutation45 permutation9
    _ = injectiveMoment H node2598 := by rfl

def raw6500 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 0, 0, 0], ![1, 0, -1, 0]]

def raw6500step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem canonical6500 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6500 = injectiveMoment H node1054 := by
  calc
    injectiveMoment H raw6500 = injectiveMoment H raw6500step0 := by
      have hz : ∀ j, raw6500 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw6500step0 = (fun i j => raw6500 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw6500 permutation104 hz
    _ = injectiveMoment H node1054 := by rfl

def raw6501 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical6501 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6501 = injectiveMoment H node2613 := by
  rfl

def raw6502 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -1, -1, 1]]

theorem canonical6502 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6502 = injectiveMoment H node2614 := by
  rfl

def raw6503 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem canonical6503 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6503 = injectiveMoment H node1054 := by
  rfl

def raw6504 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -1, -2, 2]]

theorem canonical6504 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6504 = injectiveMoment H node2615 := by
  rfl

def raw6505 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -2, 1]]

def raw6505step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical6505 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6505 = injectiveMoment H node1053 := by
  calc
    injectiveMoment H raw6505 = injectiveMoment H raw6505step0 := by
      have heq : raw6505step0 = (fun i j => raw6505 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6505 permutation10 permutation15
    _ = injectiveMoment H node1053 := by rfl

def raw6506 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![1, -1, 1, -1]]

theorem canonical6506 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6506 = injectiveMoment H node1056 := by
  rfl

def raw6507 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical6507 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6507 = injectiveMoment H node1057 := by
  rfl

def raw6508 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical6508 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6508 = injectiveMoment H node1058 := by
  rfl

def raw6509 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical6509 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6509 = injectiveMoment H node1059 := by
  rfl

def raw6510 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![1, 1, -2, 0]]

def raw6510step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0]]

def raw6510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]

theorem canonical6510 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6510 = injectiveMoment H node207 := by
  calc
    injectiveMoment H raw6510 = injectiveMoment H raw6510step0 := by
      have heq : raw6510step0 = raw6510.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6510).symm
    injectiveMoment H raw6510step0 = injectiveMoment H raw6510step1 := by
      have heq : raw6510step1 = (fun i j => raw6510step0 (permutation27 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6510step0 permutation27 permutation6
    _ = injectiveMoment H node207 := by rfl

def raw6511 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -3, 2], ![1, 0, 0, -1]]

theorem canonical6511 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6511 = injectiveMoment H node1062 := by
  rfl

def raw6512 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical6512 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6512 = injectiveMoment H node2616 := by
  rfl

def raw6513 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

theorem canonical6513 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6513 = injectiveMoment H node1063 := by
  rfl

def raw6514 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, -1, 0, 0]]

def raw6514step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0]]

theorem canonical6514 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6514 = injectiveMoment H node2616 := by
  calc
    injectiveMoment H raw6514 = injectiveMoment H raw6514step0 := by
      have heq : raw6514step0 = (fun i j => raw6514 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6514 permutation35 permutation9
    _ = injectiveMoment H node2616 := by rfl

def raw6515 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, -1, 1]]

theorem canonical6515 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6515 = injectiveMoment H node2617 := by
  rfl

def raw6516 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, 0, -2, 1]]

def raw6516step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

theorem canonical6516 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6516 = injectiveMoment H node1063 := by
  calc
    injectiveMoment H raw6516 = injectiveMoment H raw6516step0 := by
      have heq : raw6516step0 = (fun i j => raw6516 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6516 permutation10 permutation15
    _ = injectiveMoment H node1063 := by rfl

def raw6517 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -3, 1], ![1, -1, 0, 0]]

theorem canonical6517 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6517 = injectiveMoment H node1065 := by
  rfl

def raw6518 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, -1, 1]]

theorem canonical6518 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6518 = injectiveMoment H node1066 := by
  rfl

def raw6519 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![1, 1, -3, 1]]

def raw6519step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![2, -3, 1]]

def raw6519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -3, 3], ![-2, 3, -1]]

def raw6519step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0]]

theorem canonical6519 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6519 = injectiveMoment H node188 := by
  calc
    injectiveMoment H raw6519 = injectiveMoment H raw6519step0 := by
      have heq : raw6519step0 = raw6519.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6519).symm
    injectiveMoment H raw6519step0 = injectiveMoment H raw6519step1 := by
      have heq : raw6519step1 = -raw6519step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6519step0).symm
    injectiveMoment H raw6519step1 = injectiveMoment H raw6519step2 := by
      have heq : raw6519step2 = (fun i j => raw6519step1 (permutation31 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6519step1 permutation31 permutation4
    _ = injectiveMoment H node188 := by rfl

def raw6520 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 4, -4], ![1, 1, -4, 2]]

def raw6520step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 4, -4], ![2, -4, 2]]

def raw6520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -4, 4], ![-2, 4, -2]]

def raw6520step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 4, -4], ![1, -1, 0], ![1, -1, 0]]

theorem canonical6520 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6520 = injectiveMoment H node157 := by
  calc
    injectiveMoment H raw6520 = injectiveMoment H raw6520step0 := by
      have heq : raw6520step0 = raw6520.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6520).symm
    injectiveMoment H raw6520step0 = injectiveMoment H raw6520step1 := by
      have heq : raw6520step1 = -raw6520step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6520step0).symm
    injectiveMoment H raw6520step1 = injectiveMoment H raw6520step2 := by
      have heq : raw6520step2 = (fun i j => raw6520step1 (permutation31 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6520step1 permutation31 permutation4
    _ = injectiveMoment H node157 := by rfl

def raw6521 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 0, 3, -3], ![1, 0, 0, -1]]

def raw6521step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -3, 2], ![1, 0, 0, -1]]

theorem canonical6521 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6521 = injectiveMoment H node1062 := by
  calc
    injectiveMoment H raw6521 = injectiveMoment H raw6521step0 := by
      have heq : raw6521step0 = (fun i j => raw6521 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6521 permutation11 permutation9
    _ = injectiveMoment H node1062 := by rfl

def raw6522 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -1, 3, -3]]

theorem canonical6522 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6522 = injectiveMoment H node1072 := by
  rfl

def raw6523 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 1, -1]]

theorem canonical6523 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6523 = injectiveMoment H node1074 := by
  rfl

def raw6524 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical6524 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6524 = injectiveMoment H node1075 := by
  rfl

def raw6525 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -3, 2], ![1, 0, 3, -4]]

def raw6525step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -3, 3], ![2, 2, -4]]

def raw6525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![1, -1, 0], ![0, 3, -3], ![-2, -2, 4]]

def raw6525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1]]

theorem canonical6525 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw6525 = injectiveMoment H node155 := by
  calc
    injectiveMoment H raw6525 = injectiveMoment H raw6525step0 := by
      have heq : raw6525step0 = raw6525.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6525).symm
    injectiveMoment H raw6525step0 = injectiveMoment H raw6525step1 := by
      have heq : raw6525step1 = -raw6525step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw6525step0).symm
    injectiveMoment H raw6525step1 = injectiveMoment H raw6525step2 := by
      have heq : raw6525step2 = (fun i j => raw6525step1 (permutation32 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6525step1 permutation32 permutation3
    _ = injectiveMoment H node155 := by rfl

def raw6526 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 0, 2, -2], ![1, 0, 0, -1]]

def raw6526step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1]]

theorem canonical6526 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6526 = injectiveMoment H node1053 := by
  calc
    injectiveMoment H raw6526 = injectiveMoment H raw6526step0 := by
      have heq : raw6526step0 = (fun i j => raw6526 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6526 permutation11 permutation9
    _ = injectiveMoment H node1053 := by rfl

def raw6527 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 3, -3]]

def raw6527step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![-1, 1, 1, -1], ![0, -2, -1, 3], ![2, 1, 0, -3]]

def raw6527step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, 1, -1, -1]]

theorem canonical6527 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6527 = injectiveMoment H node797 := by
  calc
    injectiveMoment H raw6527 = injectiveMoment H raw6527step0 := by
      have heq : raw6527step0 = raw6527.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6527).symm
    injectiveMoment H raw6527step0 = injectiveMoment H raw6527step1 := by
      have heq : raw6527step1 = (fun i j => raw6527step0 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6527step0 permutation22 permutation23
    _ = injectiveMoment H node797 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
