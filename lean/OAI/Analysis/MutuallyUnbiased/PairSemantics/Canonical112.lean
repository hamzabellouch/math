import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw3584 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -2, 0, 1], ![1, 1, 1, -3]]

def raw3584step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 1, 0], ![-1, 2, 0, -1], ![-1, -1, -1, 3]]

def raw3584step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical3584 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3584 = injectiveMoment H node946 := by
  calc
    injectiveMoment H raw3584 = injectiveMoment H raw3584step0 := by
      have heq : raw3584step0 = -raw3584 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3584).symm
    injectiveMoment H raw3584step0 = injectiveMoment H raw3584step1 := by
      have heq : raw3584step1 = (fun i j => raw3584step0 (permutation31 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3584step0 permutation31 permutation21
    _ = injectiveMoment H node946 := by rfl

def raw3585 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -2, 2, -1], ![1, 1, -1, -1]]

def raw3585step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, -1, 2, -1], ![2, 0, -1, -1]]

def raw3585step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, 1, 0, -2]]

theorem canonical3585 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3585 = injectiveMoment H node1005 := by
  calc
    injectiveMoment H raw3585 = injectiveMoment H raw3585step0 := by
      have heq : raw3585step0 = raw3585.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3585).symm
    injectiveMoment H raw3585step0 = injectiveMoment H raw3585step1 := by
      have heq : raw3585step1 = (fun i j => raw3585step0 (permutation25 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3585step0 permutation25 permutation19
    _ = injectiveMoment H node1005 := by rfl

def raw3586 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, 0, 3, -4]]

def raw3586step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, -1, -2, 3], ![2, 0, 2, -4]]

def raw3586step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical3586 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3586 = injectiveMoment H node1189 := by
  calc
    injectiveMoment H raw3586 = injectiveMoment H raw3586step0 := by
      have heq : raw3586step0 = raw3586.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3586).symm
    injectiveMoment H raw3586step0 = injectiveMoment H raw3586step1 := by
      have heq : raw3586step1 = (fun i j => raw3586step0 (permutation22 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3586step0 permutation22 permutation15
    _ = injectiveMoment H node1189 := by rfl

def raw3587 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw3587step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, -1, -1, 2], ![2, 0, 1, -3]]

def raw3587step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical3587 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3587 = injectiveMoment H node1079 := by
  calc
    injectiveMoment H raw3587 = injectiveMoment H raw3587step0 := by
      have heq : raw3587step0 = raw3587.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3587).symm
    injectiveMoment H raw3587step0 = injectiveMoment H raw3587step1 := by
      have heq : raw3587step1 = (fun i j => raw3587step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3587step0 permutation22 permutation17
    _ = injectiveMoment H node1079 := by rfl

def raw3588 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw3588step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, -1, 1, 0], ![2, 0, -1, -1]]

def raw3588step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical3588 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3588 = injectiveMoment H node1241 := by
  calc
    injectiveMoment H raw3588 = injectiveMoment H raw3588step0 := by
      have heq : raw3588step0 = raw3588.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3588).symm
    injectiveMoment H raw3588step0 = injectiveMoment H raw3588step1 := by
      have heq : raw3588step1 = (fun i j => raw3588step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3588step0 permutation32 permutation30
    _ = injectiveMoment H node1241 := by rfl

def raw3589 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, -1, 0], ![1, 0, -2, 1], ![1, -1, 3, -3]]

def raw3589step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, 0, -1], ![0, -1, -2, 3], ![2, 0, 1, -3]]

def raw3589step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 0, -1]]

theorem canonical3589 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3589 = injectiveMoment H node816 := by
  calc
    injectiveMoment H raw3589 = injectiveMoment H raw3589step0 := by
      have heq : raw3589step0 = raw3589.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3589).symm
    injectiveMoment H raw3589step0 = injectiveMoment H raw3589step1 := by
      have heq : raw3589step1 = (fun i j => raw3589step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3589step0 permutation22 permutation17
    _ = injectiveMoment H node816 := by rfl

def raw3590 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 0, -1], ![1, -2, 1, 0], ![1, 1, -1, -1]]

def raw3590step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 0, 1, -1], ![2, -1, 0, -1]]

def raw3590step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical3590 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3590 = injectiveMoment H node1000 := by
  calc
    injectiveMoment H raw3590 = injectiveMoment H raw3590step0 := by
      have heq : raw3590step0 = raw3590.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3590).symm
    injectiveMoment H raw3590step0 = injectiveMoment H raw3590step1 := by
      have heq : raw3590step1 = (fun i j => raw3590step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3590step0 permutation31 permutation20
    _ = injectiveMoment H node1000 := by rfl

def raw3591 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 0, -1], ![1, -2, 2, -1], ![1, 1, -2, 0]]

def raw3591step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 0, 2, -2], ![2, -1, -1, 0]]

def raw3591step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, 0, -2, 2], ![-2, 1, 1, 0]]

def raw3591step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical3591 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3591 = injectiveMoment H node1010 := by
  calc
    injectiveMoment H raw3591 = injectiveMoment H raw3591step0 := by
      have heq : raw3591step0 = raw3591.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3591).symm
    injectiveMoment H raw3591step0 = injectiveMoment H raw3591step1 := by
      have heq : raw3591step1 = -raw3591step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3591step0).symm
    injectiveMoment H raw3591step1 = injectiveMoment H raw3591step2 := by
      have heq : raw3591step2 = (fun i j => raw3591step1 (permutation15 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3591step1 permutation15 permutation19
    _ = injectiveMoment H node1010 := by rfl

def raw3592 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 0, -1], ![1, -2, 3, -2], ![1, 1, -3, 1]]

def raw3592step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 0, 3, -3], ![2, -1, -2, 1]]

def raw3592step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, 0, -3, 3], ![-2, 1, 2, -1]]

def raw3592step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, 3, -3], ![0, 2, -1, -1], ![1, -2, -1, 2]]

theorem canonical3592 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3592 = injectiveMoment H node1270 := by
  calc
    injectiveMoment H raw3592 = injectiveMoment H raw3592step0 := by
      have heq : raw3592step0 = raw3592.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3592).symm
    injectiveMoment H raw3592step0 = injectiveMoment H raw3592step1 := by
      have heq : raw3592step1 = -raw3592step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3592step0).symm
    injectiveMoment H raw3592step1 = injectiveMoment H raw3592step2 := by
      have heq : raw3592step2 = (fun i j => raw3592step1 (permutation17 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3592step1 permutation17 permutation16
    _ = injectiveMoment H node1270 := by rfl

def raw3593 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw3593step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical3593 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3593 = injectiveMoment H node1110 := by
  calc
    injectiveMoment H raw3593 = injectiveMoment H raw3593step0 := by
      have heq : raw3593step0 = (fun i j => raw3593 (permutation21 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3593 permutation21 permutation23
    _ = injectiveMoment H node1110 := by rfl

def raw3594 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw3594step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -1, 0], ![0, 0, 1, -1], ![2, -1, -1, 0]]

def raw3594step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical3594 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3594 = injectiveMoment H node1242 := by
  calc
    injectiveMoment H raw3594 = injectiveMoment H raw3594step0 := by
      have heq : raw3594step0 = raw3594.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3594).symm
    injectiveMoment H raw3594step0 = injectiveMoment H raw3594step1 := by
      have heq : raw3594step1 = (fun i j => raw3594step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3594step0 permutation31 permutation20
    _ = injectiveMoment H node1242 := by rfl

def raw3595 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, -2, 1]]

def raw3595step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, 0, 1], ![-1, 1, -2, 2], ![-1, 0, 2, -1]]

def raw3595step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical3595 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3595 = injectiveMoment H node1281 := by
  calc
    injectiveMoment H raw3595 = injectiveMoment H raw3595step0 := by
      have heq : raw3595step0 = -raw3595 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3595).symm
    injectiveMoment H raw3595step0 = injectiveMoment H raw3595step1 := by
      have heq : raw3595step1 = (fun i j => raw3595step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3595step0 permutation19 permutation15
    _ = injectiveMoment H node1281 := by rfl

def raw3596 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![0, 1, -2, 1], ![2, -2, 1, -1]]

def raw3596step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![0, -1, 2, -1], ![-2, 2, -1, 1]]

def raw3596step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem canonical3596 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3596 = injectiveMoment H node520 := by
  calc
    injectiveMoment H raw3596 = injectiveMoment H raw3596step0 := by
      have heq : raw3596step0 = -raw3596 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3596).symm
    injectiveMoment H raw3596step0 = injectiveMoment H raw3596step1 := by
      have heq : raw3596step1 = (fun i j => raw3596step0 (permutation30 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3596step0 permutation30 permutation11
    _ = injectiveMoment H node520 := by rfl

def raw3597 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -2, 2, -1], ![1, 1, -3, 1]]

theorem canonical3597 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3597 = injectiveMoment H node612 := by
  rfl

def raw3598 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw3598step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw3598step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, 2, -2], ![1, 1, -1, -1]]

theorem canonical3598 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3598 = injectiveMoment H node1040 := by
  calc
    injectiveMoment H raw3598 = injectiveMoment H raw3598step0 := by
      have heq : raw3598step0 = -raw3598 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3598).symm
    injectiveMoment H raw3598step0 = injectiveMoment H raw3598step1 := by
      have heq : raw3598step1 = (fun i j => raw3598step0 (permutation19 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3598step0 permutation19 permutation17
    _ = injectiveMoment H node1040 := by rfl

def raw3599 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, -2, 1]]

def raw3599step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -1, 2], ![-1, 1, -1, 1], ![-1, 0, 2, -1]]

def raw3599step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical3599 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3599 = injectiveMoment H node1058 := by
  calc
    injectiveMoment H raw3599 = injectiveMoment H raw3599step0 := by
      have heq : raw3599step0 = -raw3599 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3599).symm
    injectiveMoment H raw3599step0 = injectiveMoment H raw3599step1 := by
      have heq : raw3599step1 = (fun i j => raw3599step0 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3599step0 permutation16 permutation17
    _ = injectiveMoment H node1058 := by rfl

def raw3600 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 2, -3], ![1, -2, 1, 0], ![1, 1, -3, 1]]

def raw3600step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 2, 1, -3], ![2, -3, 0, 1]]

def raw3600step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, -2, -1, 3], ![-2, 3, 0, -1]]

def raw3600step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -1, -1], ![2, -1, -1, 0]]

theorem canonical3600 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3600 = injectiveMoment H node590 := by
  calc
    injectiveMoment H raw3600 = injectiveMoment H raw3600step0 := by
      have heq : raw3600step0 = raw3600.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3600).symm
    injectiveMoment H raw3600step0 = injectiveMoment H raw3600step1 := by
      have heq : raw3600step1 = -raw3600step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3600step0).symm
    injectiveMoment H raw3600step1 = injectiveMoment H raw3600step2 := by
      have heq : raw3600step2 = (fun i j => raw3600step1 (permutation32 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3600step1 permutation32 permutation12
    _ = injectiveMoment H node590 := by rfl

def raw3601 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 2, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw3601step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -2, 3], ![-1, 1, 1, -1], ![-1, 0, 1, 0]]

def raw3601step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical3601 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3601 = injectiveMoment H node805 := by
  calc
    injectiveMoment H raw3601 = injectiveMoment H raw3601step0 := by
      have heq : raw3601step0 = -raw3601 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3601).symm
    injectiveMoment H raw3601step0 = injectiveMoment H raw3601step1 := by
      have heq : raw3601step1 = (fun i j => raw3601step0 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3601step0 permutation16 permutation17
    _ = injectiveMoment H node805 := by rfl

def raw3602 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw3602step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 0, 2, -1]]

def raw3602step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical3602 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3602 = injectiveMoment H node807 := by
  calc
    injectiveMoment H raw3602 = injectiveMoment H raw3602step0 := by
      have heq : raw3602step0 = -raw3602 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3602).symm
    injectiveMoment H raw3602step0 = injectiveMoment H raw3602step1 := by
      have heq : raw3602step1 = (fun i j => raw3602step0 (permutation16 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3602step0 permutation16 permutation17
    _ = injectiveMoment H node807 := by rfl

def raw3603 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -3, 2]]

def raw3603step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -2, 3], ![-1, 1, -1, 1], ![-1, 0, 3, -2]]

def raw3603step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical3603 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3603 = injectiveMoment H node1215 := by
  calc
    injectiveMoment H raw3603 = injectiveMoment H raw3603step0 := by
      have heq : raw3603step0 = -raw3603 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3603).symm
    injectiveMoment H raw3603step0 = injectiveMoment H raw3603step1 := by
      have heq : raw3603step1 = (fun i j => raw3603step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3603step0 permutation19 permutation15
    _ = injectiveMoment H node1215 := by rfl

def raw3604 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, -2, -1, 2], ![1, 1, -2, 0]]

def raw3604step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 3, -1, -2], ![2, -4, 2, 0]]

def raw3604step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, -3, 1, 2], ![-2, 4, -2, 0]]

def raw3604step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, 1, -3], ![2, -1, -1, 0]]

theorem canonical3604 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3604 = injectiveMoment H node580 := by
  calc
    injectiveMoment H raw3604 = injectiveMoment H raw3604step0 := by
      have heq : raw3604step0 = raw3604.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3604).symm
    injectiveMoment H raw3604step0 = injectiveMoment H raw3604step1 := by
      have heq : raw3604step1 = -raw3604step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3604step0).symm
    injectiveMoment H raw3604step1 = injectiveMoment H raw3604step2 := by
      have heq : raw3604step2 = (fun i j => raw3604step1 (permutation30 i) (permutation14 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3604step1 permutation30 permutation14
    _ = injectiveMoment H node580 := by rfl

def raw3605 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, -2, 0, 1], ![1, 1, -3, 1]]

def raw3605step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 1, -2, 1], ![0, 3, 0, -3], ![2, -4, 1, 1]]

def raw3605step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -1, 2, -1], ![0, -3, 0, 3], ![-2, 4, -1, -1]]

def raw3605step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 3, -3], ![0, 2, -1, -1], ![2, -1, -1, 0]]

theorem canonical3605 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3605 = injectiveMoment H node462 := by
  calc
    injectiveMoment H raw3605 = injectiveMoment H raw3605step0 := by
      have heq : raw3605step0 = raw3605.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3605).symm
    injectiveMoment H raw3605step0 = injectiveMoment H raw3605step1 := by
      have heq : raw3605step1 = -raw3605step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3605step0).symm
    injectiveMoment H raw3605step1 = injectiveMoment H raw3605step2 := by
      have heq : raw3605step2 = (fun i j => raw3605step1 (permutation32 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3605step1 permutation32 permutation12
    _ = injectiveMoment H node462 := by rfl

def raw3606 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, -1, -2, 2], ![1, 0, -1, 0]]

def raw3606step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -3, 4], ![-1, 1, 2, -2], ![-1, 0, 1, 0]]

def raw3606step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 2, 0, -2], ![1, -1, 2, -2]]

theorem canonical3606 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3606 = injectiveMoment H node1169 := by
  calc
    injectiveMoment H raw3606 = injectiveMoment H raw3606step0 := by
      have heq : raw3606step0 = -raw3606 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3606).symm
    injectiveMoment H raw3606step0 = injectiveMoment H raw3606step1 := by
      have heq : raw3606step1 = (fun i j => raw3606step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3606step0 permutation19 permutation15
    _ = injectiveMoment H node1169 := by rfl

def raw3607 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -2, 1]]

def raw3607step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -3, 4], ![-1, 1, 1, -1], ![-1, 0, 2, -1]]

def raw3607step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical3607 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3607 = injectiveMoment H node1173 := by
  calc
    injectiveMoment H raw3607 = injectiveMoment H raw3607step0 := by
      have heq : raw3607step0 = -raw3607 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3607).symm
    injectiveMoment H raw3607step0 = injectiveMoment H raw3607step1 := by
      have heq : raw3607step1 = (fun i j => raw3607step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3607step0 permutation19 permutation15
    _ = injectiveMoment H node1173 := by rfl

def raw3608 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -3, 2]]

def raw3608step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -3, 4], ![-1, 1, 0, 0], ![-1, 0, 3, -2]]

def raw3608step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem canonical3608 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3608 = injectiveMoment H node1175 := by
  calc
    injectiveMoment H raw3608 = injectiveMoment H raw3608step0 := by
      have heq : raw3608step0 = -raw3608 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3608).symm
    injectiveMoment H raw3608step0 = injectiveMoment H raw3608step1 := by
      have heq : raw3608step1 = (fun i j => raw3608step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3608step0 permutation19 permutation15
    _ = injectiveMoment H node1175 := by rfl

def raw3609 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, 0, -3, 2], ![1, -1, 0, 0]]

def raw3609step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -3, 4], ![-1, 0, 3, -2], ![-1, 1, 0, 0]]

def raw3609step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 3, -2], ![0, 2, 0, -2], ![1, -1, 0, 0]]

theorem canonical3609 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3609 = injectiveMoment H node1175 := by
  calc
    injectiveMoment H raw3609 = injectiveMoment H raw3609step0 := by
      have heq : raw3609step0 = -raw3609 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3609).symm
    injectiveMoment H raw3609step0 = injectiveMoment H raw3609step1 := by
      have heq : raw3609step1 = (fun i j => raw3609step0 (permutation17 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3609step0 permutation17 permutation15
    _ = injectiveMoment H node1175 := by rfl

def raw3610 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 1, 3, -4], ![1, 0, -2, 1], ![1, -1, -1, 1]]

def raw3610step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -1, -3, 4], ![-1, 0, 2, -1], ![-1, 1, 1, -1]]

def raw3610step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical3610 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3610 = injectiveMoment H node1173 := by
  calc
    injectiveMoment H raw3610 = injectiveMoment H raw3610step0 := by
      have heq : raw3610step0 = -raw3610 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3610).symm
    injectiveMoment H raw3610step0 = injectiveMoment H raw3610step1 := by
      have heq : raw3610step1 = (fun i j => raw3610step0 (permutation17 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3610step0 permutation17 permutation15
    _ = injectiveMoment H node1173 := by rfl

def raw3611 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -2, 0, 1], ![1, 0, 3, -4]]

def raw3611step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![0, -3, 0, 3], ![2, 1, 1, -4]]

def raw3611step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![0, 3, 0, -3], ![-2, -1, -1, 4]]

def raw3611step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 0, 3, -3], ![0, 2, -2, 0], ![2, -1, 0, -1]]

theorem canonical3611 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3611 = injectiveMoment H node461 := by
  calc
    injectiveMoment H raw3611 = injectiveMoment H raw3611step0 := by
      have heq : raw3611step0 = raw3611.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3611).symm
    injectiveMoment H raw3611step0 = injectiveMoment H raw3611step1 := by
      have heq : raw3611step1 = -raw3611step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3611step0).symm
    injectiveMoment H raw3611step1 = injectiveMoment H raw3611step2 := by
      have heq : raw3611step2 = (fun i j => raw3611step1 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3611step1 permutation32 permutation11
    _ = injectiveMoment H node461 := by rfl

def raw3612 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -2, 1, 0], ![1, 0, 2, -3]]

def raw3612step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, 3, -1], ![-1, 2, -1, 0], ![-1, 0, -2, 3]]

def raw3612step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![2, -1, 0, -1]]

theorem canonical3612 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3612 = injectiveMoment H node589 := by
  calc
    injectiveMoment H raw3612 = injectiveMoment H raw3612step0 := by
      have heq : raw3612step0 = -raw3612 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3612).symm
    injectiveMoment H raw3612step0 = injectiveMoment H raw3612step1 := by
      have heq : raw3612step1 = (fun i j => raw3612step0 (permutation19 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3612step0 permutation19 permutation16
    _ = injectiveMoment H node589 := by rfl

def raw3613 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -2, 2, -1], ![1, 0, 1, -2]]

def raw3613step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![0, -2, 3, -1], ![-1, 2, -2, 1], ![-1, 0, -1, 2]]

def raw3613step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, -1, 1, -2]]

theorem canonical3613 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3613 = injectiveMoment H node588 := by
  calc
    injectiveMoment H raw3613 = injectiveMoment H raw3613step0 := by
      have heq : raw3613step0 = -raw3613 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3613).symm
    injectiveMoment H raw3613step0 = injectiveMoment H raw3613step1 := by
      have heq : raw3613step1 = (fun i j => raw3613step0 (permutation19 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3613step0 permutation19 permutation16
    _ = injectiveMoment H node588 := by rfl

def raw3614 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -2, 3, -2], ![1, 0, 0, -1]]

def raw3614step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -2, 0], ![0, -3, 3, 0], ![2, 1, -2, -1]]

def raw3614step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![0, -2, 2, 0], ![0, 3, -3, 0], ![-2, -1, 2, 1]]

def raw3614step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 2, 0, -1], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, -2, -1, 2]]

theorem canonical3614 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw3614 = injectiveMoment H node1376 := by
  calc
    injectiveMoment H raw3614 = injectiveMoment H raw3614step0 := by
      have heq : raw3614step0 = raw3614.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3614).symm
    injectiveMoment H raw3614step0 = injectiveMoment H raw3614step1 := by
      have heq : raw3614step1 = -raw3614step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw3614step0).symm
    injectiveMoment H raw3614step1 = injectiveMoment H raw3614step2 := by
      have heq : raw3614step2 = (fun i j => raw3614step1 (permutation9 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3614step1 permutation9 permutation27
    _ = injectiveMoment H node1376 := by rfl

def raw3615 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, 2, -3, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

def raw3615step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![0, -3, 0, 3], ![2, 1, 0, -3]]

def raw3615step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, 0, -3, 3], ![0, 2, 1, -3], ![1, -2, 0, 1]]

theorem canonical3615 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw3615 = injectiveMoment H node1313 := by
  calc
    injectiveMoment H raw3615 = injectiveMoment H raw3615step0 := by
      have heq : raw3615step0 = raw3615.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw3615).symm
    injectiveMoment H raw3615step0 = injectiveMoment H raw3615step1 := by
      have heq : raw3615step1 = (fun i j => raw3615step0 (permutation18 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw3615step0 permutation18 permutation21
    _ = injectiveMoment H node1313 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
