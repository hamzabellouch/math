import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3488 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, -2, 0, 0]]

def raw3488step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical3488 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3488 = injectiveMoment H node2745 := by
  calc
    injectiveMoment H raw3488 = injectiveMoment H raw3488step0 := by
      have heq : raw3488step0 = (fun i j => raw3488 (permutation83 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3488 permutation83 permutation22
    _ = injectiveMoment H node2745 := by rfl

def raw3489 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -2, 0]]

def raw3489step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 2, -1, 0], ![-1, -1, 2, 0]]

def raw3489step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical3489 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3489 = injectiveMoment H node2023 := by
  calc
    injectiveMoment H raw3489 = injectiveMoment H raw3489step0 := by
      have heq : raw3489step0 = -raw3489 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3489).symm
    injectiveMoment H raw3489step0 = injectiveMoment H raw3489step1 := by
      have heq : raw3489step1 = (fun i j => raw3489step0 (permutation56 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3489step0 permutation56 permutation30
    _ = injectiveMoment H node2023 := by rfl

def raw3490 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw3490step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem canonical3490 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3490 = injectiveMoment H node2759 := by
  calc
    injectiveMoment H raw3490 = injectiveMoment H raw3490step0 := by
      have heq : raw3490step0 = (fun i j => raw3490 (permutation122 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3490 permutation122 permutation18
    _ = injectiveMoment H node2759 := by rfl

def raw3491 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -1, -1, 0]]

def raw3491step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem canonical3491 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3491 = injectiveMoment H node1054 := by
  calc
    injectiveMoment H raw3491 = injectiveMoment H raw3491step0 := by
      have heq : raw3491step0 = (fun i j => raw3491 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3491 permutation27 permutation18
    _ = injectiveMoment H node1054 := by rfl

def raw3492 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 1, -1]]

def raw3492step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

theorem canonical3492 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3492 = injectiveMoment H node2003 := by
  calc
    injectiveMoment H raw3492 = injectiveMoment H raw3492step0 := by
      have heq : raw3492step0 = (fun i j => raw3492 (permutation39 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3492 permutation39 permutation11
    _ = injectiveMoment H node2003 := by rfl

def raw3493 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -2, 0, 0]]

def raw3493step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical3493 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3493 = injectiveMoment H node1057 := by
  calc
    injectiveMoment H raw3493 = injectiveMoment H raw3493step0 := by
      have heq : raw3493step0 = (fun i j => raw3493 (permutation25 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3493 permutation25 permutation25
    _ = injectiveMoment H node1057 := by rfl

def raw3494 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

def raw3494step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 1, 1, -2], ![2, -1, -1, 0]]

def raw3494step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical3494 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3494 = injectiveMoment H node1000 := by
  calc
    injectiveMoment H raw3494 = injectiveMoment H raw3494step0 := by
      have heq : raw3494step0 = raw3494.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3494).symm
    injectiveMoment H raw3494step0 = injectiveMoment H raw3494step1 := by
      have heq : raw3494step1 = (fun i j => raw3494step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3494step0 permutation29 permutation18
    _ = injectiveMoment H node1000 := by rfl

def raw3495 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 1, -1], ![1, -1, 2, -2], ![1, 1, -3, 1]]

def raw3495step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -1, 1], ![-1, 1, -2, 2], ![-1, -1, 3, -1]]

def raw3495step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 2, -2]]

theorem canonical3495 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3495 = injectiveMoment H node971 := by
  calc
    injectiveMoment H raw3495 = injectiveMoment H raw3495step0 := by
      have heq : raw3495step0 = -raw3495 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3495).symm
    injectiveMoment H raw3495step0 = injectiveMoment H raw3495step1 := by
      have heq : raw3495step1 = (fun i j => raw3495step0 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3495step0 permutation29 permutation16
    _ = injectiveMoment H node971 := by rfl

def raw3496 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -3, 2], ![2, -1, 1, -2]]

def raw3496step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -2, 2], ![0, -1, 3, -2], ![-2, 1, -1, 2]]

def raw3496step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, -1, 2]]

theorem canonical3496 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3496 = injectiveMoment H node1322 := by
  calc
    injectiveMoment H raw3496 = injectiveMoment H raw3496step0 := by
      have heq : raw3496step0 = -raw3496 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3496).symm
    injectiveMoment H raw3496step0 = injectiveMoment H raw3496step1 := by
      have heq : raw3496step1 = (fun i j => raw3496step0 (permutation23 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3496step0 permutation23 permutation15
    _ = injectiveMoment H node1322 := by rfl

def raw3497 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

theorem canonical3497 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3497 = injectiveMoment H node2036 := by
  rfl

def raw3498 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -1, 0, -1]]

def raw3498step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -2, 0, 1]]

theorem canonical3498 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3498 = injectiveMoment H node1314 := by
  calc
    injectiveMoment H raw3498 = injectiveMoment H raw3498step0 := by
      have heq : raw3498step0 = (fun i j => raw3498 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3498 permutation27 permutation17
    _ = injectiveMoment H node1314 := by rfl

def raw3499 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def raw3499step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

theorem canonical3499 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3499 = injectiveMoment H node2036 := by
  calc
    injectiveMoment H raw3499 = injectiveMoment H raw3499step0 := by
      have heq : raw3499step0 = (fun i j => raw3499 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3499 permutation35 permutation9
    _ = injectiveMoment H node2036 := by rfl

def raw3500 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw3500step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical3500 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3500 = injectiveMoment H node2001 := by
  calc
    injectiveMoment H raw3500 = injectiveMoment H raw3500step0 := by
      have heq : raw3500step0 = (fun i j => raw3500 (permutation77 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3500 permutation77 permutation29
    _ = injectiveMoment H node2001 := by rfl

def raw3501 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw3501step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem canonical3501 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3501 = injectiveMoment H node2635 := by
  calc
    injectiveMoment H raw3501 = injectiveMoment H raw3501step0 := by
      have heq : raw3501step0 = (fun i j => raw3501 (permutation108 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3501 permutation108 permutation17
    _ = injectiveMoment H node2635 := by rfl

def raw3502 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw3502step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, 1, 0], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical3502 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3502 = injectiveMoment H node2633 := by
  calc
    injectiveMoment H raw3502 = injectiveMoment H raw3502step0 := by
      have heq : raw3502step0 = (fun i j => raw3502 (permutation122 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3502 permutation122 permutation17
    _ = injectiveMoment H node2633 := by rfl

def raw3503 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -1, -2, 1]]

def raw3503step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 2, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical3503 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3503 = injectiveMoment H node854 := by
  calc
    injectiveMoment H raw3503 = injectiveMoment H raw3503step0 := by
      have heq : raw3503step0 = (fun i j => raw3503 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3503 permutation27 permutation17
    _ = injectiveMoment H node854 := by rfl

def raw3504 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 2, -3, 1], ![2, -2, 1, -1]]

def raw3504step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -2, 2], ![0, -2, 3, -1], ![-2, 2, -1, 1]]

def raw3504step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, -2, 1, -1]]

theorem canonical3504 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3504 = injectiveMoment H node591 := by
  calc
    injectiveMoment H raw3504 = injectiveMoment H raw3504step0 := by
      have heq : raw3504step0 = -raw3504 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3504).symm
    injectiveMoment H raw3504step0 = injectiveMoment H raw3504step1 := by
      have heq : raw3504step1 = (fun i j => raw3504step0 (permutation23 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3504step0 permutation23 permutation16
    _ = injectiveMoment H node591 := by rfl

def raw3505 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw3505step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical3505 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3505 = injectiveMoment H node2001 := by
  calc
    injectiveMoment H raw3505 = injectiveMoment H raw3505step0 := by
      have heq : raw3505step0 = (fun i j => raw3505 (permutation83 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3505 permutation83 permutation22
    _ = injectiveMoment H node2001 := by rfl

def raw3506 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw3506step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical3506 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3506 = injectiveMoment H node1112 := by
  calc
    injectiveMoment H raw3506 = injectiveMoment H raw3506step0 := by
      have heq : raw3506step0 = (fun i j => raw3506 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3506 permutation21 permutation17
    _ = injectiveMoment H node1112 := by rfl

def raw3507 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw3507step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -2, 2], ![-1, 1, 0, 0], ![-1, -1, 2, 0]]

def raw3507step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical3507 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3507 = injectiveMoment H node1057 := by
  calc
    injectiveMoment H raw3507 = injectiveMoment H raw3507step0 := by
      have heq : raw3507step0 = -raw3507 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3507).symm
    injectiveMoment H raw3507step0 = injectiveMoment H raw3507step1 := by
      have heq : raw3507step1 = (fun i j => raw3507step0 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3507step0 permutation29 permutation16
    _ = injectiveMoment H node1057 := by rfl

def raw3508 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 2, -2], ![1, -1, 1, -1], ![1, 1, -3, 1]]

def raw3508step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -2, 2], ![-1, 1, -1, 1], ![-1, -1, 3, -1]]

def raw3508step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, -1, 1, -1]]

theorem canonical3508 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3508 = injectiveMoment H node975 := by
  calc
    injectiveMoment H raw3508 = injectiveMoment H raw3508step0 := by
      have heq : raw3508step0 = -raw3508 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3508).symm
    injectiveMoment H raw3508step0 = injectiveMoment H raw3508step1 := by
      have heq : raw3508step1 = (fun i j => raw3508step0 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3508step0 permutation29 permutation16
    _ = injectiveMoment H node975 := by rfl

def raw3509 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 0, 3, -3], ![1, -1, 0, 0], ![1, 1, -3, 1]]

def raw3509step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, 0, -3, 3], ![-1, 1, 0, 0], ![-1, -1, 3, -1]]

def raw3509step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical3509 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3509 = injectiveMoment H node979 := by
  calc
    injectiveMoment H raw3509 = injectiveMoment H raw3509step0 := by
      have heq : raw3509step0 = -raw3509 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3509).symm
    injectiveMoment H raw3509step0 = injectiveMoment H raw3509step1 := by
      have heq : raw3509step1 = (fun i j => raw3509step0 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3509step0 permutation29 permutation16
    _ = injectiveMoment H node979 := by rfl

def raw3510 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

theorem canonical3510 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3510 = injectiveMoment H node2037 := by
  rfl

def raw3511 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 0, -1], ![2, -2, 3, -3]]

def raw3511step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -3, 0, 3], ![2, 2, -1, -3]]

def raw3511step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![0, 3, 0, -3], ![-2, -2, 1, 3]]

def raw3511step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, 0, -2], ![1, -2, -2, 3]]

theorem canonical3511 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3511 = injectiveMoment H node1271 := by
  calc
    injectiveMoment H raw3511 = injectiveMoment H raw3511step0 := by
      have heq : raw3511step0 = raw3511.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3511).symm
    injectiveMoment H raw3511step0 = injectiveMoment H raw3511step1 := by
      have heq : raw3511step1 = -raw3511step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3511step0).symm
    injectiveMoment H raw3511step1 = injectiveMoment H raw3511step2 := by
      have heq : raw3511step2 = (fun i j => raw3511step1 (permutation17 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3511step1 permutation17 permutation21
    _ = injectiveMoment H node1271 := by rfl

def raw3512 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 1, -2], ![2, -2, 2, -2]]

theorem canonical3512 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3512 = injectiveMoment H node610 := by
  rfl

def raw3513 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical3513 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3513 = injectiveMoment H node2038 := by
  rfl

def raw3514 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw3514step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, -3, 3, 0], ![2, 2, -4, 0]]

def raw3514step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![0, 3, -3, 0], ![-2, -2, 4, 0]]

def raw3514step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![2, -2, 0, 0]]

theorem canonical3514 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3514 = injectiveMoment H node582 := by
  calc
    injectiveMoment H raw3514 = injectiveMoment H raw3514step0 := by
      have heq : raw3514step0 = raw3514.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3514).symm
    injectiveMoment H raw3514step0 = injectiveMoment H raw3514step1 := by
      have heq : raw3514step1 = -raw3514step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3514step0).symm
    injectiveMoment H raw3514step1 = injectiveMoment H raw3514step2 := by
      have heq : raw3514step2 = (fun i j => raw3514step1 (permutation32 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3514step1 permutation32 permutation13
    _ = injectiveMoment H node582 := by rfl

def raw3515 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw3515step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, -3, 1, 2], ![2, 2, 0, -4]]

def raw3515step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, 3, -1, -2], ![-2, -2, 0, 4]]

def raw3515step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, -1, 0, -1]]

theorem canonical3515 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3515 = injectiveMoment H node581 := by
  calc
    injectiveMoment H raw3515 = injectiveMoment H raw3515step0 := by
      have heq : raw3515step0 = raw3515.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3515).symm
    injectiveMoment H raw3515step0 = injectiveMoment H raw3515step1 := by
      have heq : raw3515step1 = -raw3515step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3515step0).symm
    injectiveMoment H raw3515step1 = injectiveMoment H raw3515step2 := by
      have heq : raw3515step2 = (fun i j => raw3515step1 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3515step1 permutation32 permutation11
    _ = injectiveMoment H node581 := by rfl

def raw3516 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -2, 3, -2], ![1, 1, 0, -2]]

theorem canonical3516 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3516 = injectiveMoment H node611 := by
  rfl

def raw3517 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw3517step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, -3, 0, 3], ![2, 2, 0, -4]]

def raw3517step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, -3, 3], ![0, 2, 2, -4], ![1, -2, 0, 1]]

theorem canonical3517 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3517 = injectiveMoment H node1300 := by
  calc
    injectiveMoment H raw3517 = injectiveMoment H raw3517step0 := by
      have heq : raw3517step0 = raw3517.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3517).symm
    injectiveMoment H raw3517step0 = injectiveMoment H raw3517step1 := by
      have heq : raw3517step1 = (fun i j => raw3517step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3517step0 permutation18 permutation21
    _ = injectiveMoment H node1300 := by rfl

def raw3518 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -1, 1, -1], ![1, 0, 2, -3]]

def raw3518step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 3, -2], ![-1, 1, -1, 1], ![-1, 0, -2, 3]]

def raw3518step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, -2, 3], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical3518 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3518 = injectiveMoment H node1318 := by
  calc
    injectiveMoment H raw3518 = injectiveMoment H raw3518step0 := by
      have heq : raw3518step0 = -raw3518 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3518).symm
    injectiveMoment H raw3518step0 = injectiveMoment H raw3518step1 := by
      have heq : raw3518step1 = (fun i j => raw3518step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3518step0 permutation19 permutation15
    _ = injectiveMoment H node1318 := by rfl

def raw3519 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -3, 2], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw3519step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 3, -2], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw3519step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 3, -2], ![0, -1, 0, 1], ![0, 2, 0, -2], ![1, -1, -3, 3]]

theorem canonical3519 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3519 = injectiveMoment H node1320 := by
  calc
    injectiveMoment H raw3519 = injectiveMoment H raw3519step0 := by
      have heq : raw3519step0 = -raw3519 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3519).symm
    injectiveMoment H raw3519step0 = injectiveMoment H raw3519step1 := by
      have heq : raw3519step1 = (fun i j => raw3519step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3519step0 permutation19 permutation15
    _ = injectiveMoment H node1320 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
