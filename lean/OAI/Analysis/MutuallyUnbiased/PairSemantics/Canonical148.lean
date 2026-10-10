import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4736 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, -2, 2, -2]]

def raw4736step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -2, 0, 2], ![1, 2, -1, -2]]

def raw4736step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, 2, 0, -2], ![-1, -2, 1, 2]]

def raw4736step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical4736 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4736 = injectiveMoment H node1059 := by
  calc
    injectiveMoment H raw4736 = injectiveMoment H raw4736step0 := by
      have heq : raw4736step0 = raw4736.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4736).symm
    injectiveMoment H raw4736step0 = injectiveMoment H raw4736step1 := by
      have heq : raw4736step1 = -raw4736step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4736step0).symm
    injectiveMoment H raw4736step1 = injectiveMoment H raw4736step2 := by
      have heq : raw4736step2 = (fun i j => raw4736step1 (permutation17 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4736step1 permutation17 permutation21
    _ = injectiveMoment H node1059 := by rfl

def raw4737 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, -2, 1, -1]]

def raw4737step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 2, -2], ![0, -1, -1, 2], ![-2, 2, -1, 1]]

def raw4737step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 2, 1], ![0, -1, -1, 2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

theorem canonical4737 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4737 = injectiveMoment H node521 := by
  calc
    injectiveMoment H raw4737 = injectiveMoment H raw4737step0 := by
      have heq : raw4737step0 = -raw4737 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4737).symm
    injectiveMoment H raw4737step0 = injectiveMoment H raw4737step1 := by
      have heq : raw4737step1 = (fun i j => raw4737step0 (permutation32 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4737step0 permutation32 permutation11
    _ = injectiveMoment H node521 := by rfl

def raw4738 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw4738step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 2, -2], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 1, 0, 0]]

def raw4738step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical4738 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4738 = injectiveMoment H node1646 := by
  calc
    injectiveMoment H raw4738 = injectiveMoment H raw4738step0 := by
      have heq : raw4738step0 = -raw4738 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4738).symm
    injectiveMoment H raw4738step0 = injectiveMoment H raw4738step1 := by
      have heq : raw4738step1 = (fun i j => raw4738step0 (permutation83 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4738step0 permutation83 permutation23
    _ = injectiveMoment H node1646 := by rfl

def raw4739 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw4739step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 2, -2], ![0, -1, -2, 3], ![-2, 2, 0, 0]]

def raw4739step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem canonical4739 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4739 = injectiveMoment H node472 := by
  calc
    injectiveMoment H raw4739 = injectiveMoment H raw4739step0 := by
      have heq : raw4739step0 = -raw4739 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4739).symm
    injectiveMoment H raw4739step0 = injectiveMoment H raw4739step1 := by
      have heq : raw4739step1 = (fun i j => raw4739step0 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4739step0 permutation22 permutation23
    _ = injectiveMoment H node472 := by rfl

def raw4740 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical4740 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4740 = injectiveMoment H node2276 := by
  rfl

def raw4741 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, -1, -1, 1]]

def raw4741step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, -1, 0, 0]]

theorem canonical4741 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4741 = injectiveMoment H node2276 := by
  calc
    injectiveMoment H raw4741 = injectiveMoment H raw4741step0 := by
      have heq : raw4741step0 = (fun i j => raw4741 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4741 permutation34 permutation9
    _ = injectiveMoment H node2276 := by rfl

def raw4742 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![2, -2, -1, 1]]

def raw4742step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -2, 3, -1], ![1, 2, -4, 1]]

def raw4742step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![0, 2, -3, 1], ![-1, -2, 4, -1]]

def raw4742step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -2, 0], ![2, 0, 1, -3]]

theorem canonical4742 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4742 = injectiveMoment H node448 := by
  calc
    injectiveMoment H raw4742 = injectiveMoment H raw4742step0 := by
      have heq : raw4742step0 = raw4742.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4742).symm
    injectiveMoment H raw4742step0 = injectiveMoment H raw4742step1 := by
      have heq : raw4742step1 = -raw4742step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4742step0).symm
    injectiveMoment H raw4742step1 = injectiveMoment H raw4742step2 := by
      have heq : raw4742step2 = (fun i j => raw4742step1 (permutation29 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4742step1 permutation29 permutation16
    _ = injectiveMoment H node448 := by rfl

def raw4743 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw4743step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 2, -2], ![-1, 2, 0, -1], ![-1, -1, -2, 4]]

def raw4743step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem canonical4743 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4743 = injectiveMoment H node449 := by
  calc
    injectiveMoment H raw4743 = injectiveMoment H raw4743step0 := by
      have heq : raw4743step0 = -raw4743 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4743).symm
    injectiveMoment H raw4743step0 = injectiveMoment H raw4743step1 := by
      have heq : raw4743step1 = (fun i j => raw4743step0 (permutation31 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4743step0 permutation31 permutation21
    _ = injectiveMoment H node449 := by rfl

def raw4744 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw4744step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![0, -2, 1, 1], ![1, 2, 0, -3]]

def raw4744step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![0, 2, -1, -1], ![-1, -2, 0, 3]]

def raw4744step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical4744 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4744 = injectiveMoment H node473 := by
  calc
    injectiveMoment H raw4744 = injectiveMoment H raw4744step0 := by
      have heq : raw4744step0 = raw4744.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4744).symm
    injectiveMoment H raw4744step0 = injectiveMoment H raw4744step1 := by
      have heq : raw4744step1 = -raw4744step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4744step0).symm
    injectiveMoment H raw4744step1 = injectiveMoment H raw4744step2 := by
      have heq : raw4744step2 = (fun i j => raw4744step1 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4744step1 permutation29 permutation15
    _ = injectiveMoment H node473 := by rfl

def raw4745 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -2, 3, -2], ![1, 1, -1, -1]]

def raw4745step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![0, -2, 3, -1], ![1, 2, -2, -1]]

def raw4745step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

theorem canonical4745 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4745 = injectiveMoment H node484 := by
  calc
    injectiveMoment H raw4745 = injectiveMoment H raw4745step0 := by
      have heq : raw4745step0 = raw4745.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4745).symm
    injectiveMoment H raw4745step0 = injectiveMoment H raw4745step1 := by
      have heq : raw4745step1 = (fun i j => raw4745step0 (permutation21 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4745step0 permutation21 permutation19
    _ = injectiveMoment H node484 := by rfl

def raw4746 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw4746step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical4746 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4746 = injectiveMoment H node1348 := by
  calc
    injectiveMoment H raw4746 = injectiveMoment H raw4746step0 := by
      have heq : raw4746step0 = (fun i j => raw4746 (permutation24 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4746 permutation24 permutation15
    _ = injectiveMoment H node1348 := by rfl

def raw4747 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw4747step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -2, 0, 2], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical4747 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4747 = injectiveMoment H node1296 := by
  calc
    injectiveMoment H raw4747 = injectiveMoment H raw4747step0 := by
      have heq : raw4747step0 = (fun i j => raw4747 (permutation24 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4747 permutation24 permutation17
    _ = injectiveMoment H node1296 := by rfl

def raw4748 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw4748step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![0, -2, 3, -1], ![1, 2, -3, 0]]

def raw4748step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical4748 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4748 = injectiveMoment H node803 := by
  calc
    injectiveMoment H raw4748 = injectiveMoment H raw4748step0 := by
      have heq : raw4748step0 = raw4748.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4748).symm
    injectiveMoment H raw4748step0 = injectiveMoment H raw4748step1 := by
      have heq : raw4748step1 = (fun i j => raw4748step0 (permutation24 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4748step0 permutation24 permutation29
    _ = injectiveMoment H node803 := by rfl

def raw4749 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, 0, -1, 0], ![1, -1, 3, -3]]

def raw4749step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, 0, -1], ![0, -2, -1, 3], ![1, 2, 0, -3]]

def raw4749step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical4749 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4749 = injectiveMoment H node803 := by
  calc
    injectiveMoment H raw4749 = injectiveMoment H raw4749step0 := by
      have heq : raw4749step0 = raw4749.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4749).symm
    injectiveMoment H raw4749step0 = injectiveMoment H raw4749step1 := by
      have heq : raw4749step1 = (fun i j => raw4749step0 (permutation24 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4749step0 permutation24 permutation23
    _ = injectiveMoment H node803 := by rfl

def raw4750 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![1, 0, 3, -4], ![1, -1, -1, 1]]

def raw4750step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical4750 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4750 = injectiveMoment H node1348 := by
  calc
    injectiveMoment H raw4750 = injectiveMoment H raw4750step0 := by
      have heq : raw4750step0 = (fun i j => raw4750 (permutation30 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4750 permutation30 permutation15
    _ = injectiveMoment H node1348 := by rfl

def raw4751 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw4751step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw4751step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical4751 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4751 = injectiveMoment H node1576 := by
  calc
    injectiveMoment H raw4751 = injectiveMoment H raw4751step0 := by
      have heq : raw4751step0 = -raw4751 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4751).symm
    injectiveMoment H raw4751step0 = injectiveMoment H raw4751step1 := by
      have heq : raw4751step1 = (fun i j => raw4751step0 (permutation130 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4751step0 permutation130 permutation23
    _ = injectiveMoment H node1576 := by rfl

def raw4752 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -2, 2], ![0, 1, 3, -4], ![2, -2, 0, 0]]

def raw4752step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, 0, 0]]

theorem canonical4752 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4752 = injectiveMoment H node2270 := by
  calc
    injectiveMoment H raw4752 = injectiveMoment H raw4752step0 := by
      have heq : raw4752step0 = (fun i j => raw4752 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4752 permutation39 permutation9
    _ = injectiveMoment H node2270 := by rfl

def raw4753 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -2, 2], ![1, -2, 1, 0], ![1, 1, 2, -4]]

def raw4753step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -2, 2], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

theorem canonical4753 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4753 = injectiveMoment H node2271 := by
  calc
    injectiveMoment H raw4753 = injectiveMoment H raw4753step0 := by
      have heq : raw4753step0 = (fun i j => raw4753 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4753 permutation39 permutation9
    _ = injectiveMoment H node2271 := by rfl

def raw4754 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![2, -2, 0, 0]]

def raw4754step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, -1, -2, 3], ![-2, 2, 0, 0]]

def raw4754step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical4754 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4754 = injectiveMoment H node1654 := by
  calc
    injectiveMoment H raw4754 = injectiveMoment H raw4754step0 := by
      have heq : raw4754step0 = -raw4754 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4754).symm
    injectiveMoment H raw4754step0 = injectiveMoment H raw4754step1 := by
      have heq : raw4754step1 = (fun i j => raw4754step0 (permutation108 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4754step0 permutation108 permutation23
    _ = injectiveMoment H node1654 := by rfl

def raw4755 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![2, -2, -1, 1]]

theorem canonical4755 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4755 = injectiveMoment H node2278 := by
  rfl

def raw4756 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 0, 1], ![1, 1, 2, -4]]

def raw4756step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, 0, -1], ![-1, -1, -2, 4]]

def raw4756step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical4756 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4756 = injectiveMoment H node1580 := by
  calc
    injectiveMoment H raw4756 = injectiveMoment H raw4756step0 := by
      have heq : raw4756step0 = -raw4756 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4756).symm
    injectiveMoment H raw4756step0 = injectiveMoment H raw4756step1 := by
      have heq : raw4756step1 = (fun i j => raw4756step0 (permutation145 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4756step0 permutation145 permutation21
    _ = injectiveMoment H node1580 := by rfl

def raw4757 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 1, -3]]

def raw4757step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

theorem canonical4757 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4757 = injectiveMoment H node2064 := by
  calc
    injectiveMoment H raw4757 = injectiveMoment H raw4757step0 := by
      have heq : raw4757step0 = (fun i j => raw4757 (permutation33 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4757 permutation33 permutation11
    _ = injectiveMoment H node2064 := by rfl

def raw4758 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 3, -4]]

def raw4758step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical4758 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4758 = injectiveMoment H node2845 := by
  calc
    injectiveMoment H raw4758 = injectiveMoment H raw4758step0 := by
      have heq : raw4758step0 = (fun i j => raw4758 (permutation113 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4758 permutation113 permutation15
    _ = injectiveMoment H node2845 := by rfl

def raw4759 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, 3, -3], ![1, 0, -1, 0]]

def raw4759step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -3, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -2, 1, 0]]

theorem canonical4759 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4759 = injectiveMoment H node2836 := by
  calc
    injectiveMoment H raw4759 = injectiveMoment H raw4759step0 := by
      have heq : raw4759step0 = (fun i j => raw4759 (permutation113 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4759 permutation113 permutation16
    _ = injectiveMoment H node2836 := by rfl

def raw4760 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, -1, 0], ![2, -2, 2, -2]]

def raw4760step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![1, 0, 0, 1, -2], ![0, -1, 0, -1, 2], ![1, 1, 0, 0, -2]]

def raw4760step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![0, -1, -1, 2], ![1, 1, 0, -2]]

def raw4760step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical4760 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4760 = injectiveMoment H node1033 := by
  calc
    injectiveMoment H raw4760 = injectiveMoment H raw4760step0 := by
      have heq : raw4760step0 = raw4760.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4760).symm
    injectiveMoment H raw4760step0 = injectiveMoment H raw4760step1 := by
      have hz : ∀ i, raw4760step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw4760step1 = (fun i j => raw4760step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4760step0 permutation80 hz
    injectiveMoment H raw4760step1 = injectiveMoment H raw4760step2 := by
      have heq : raw4760step2 = (fun i j => raw4760step1 (permutation21 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4760step1 permutation21 permutation17
    _ = injectiveMoment H node1033 := by rfl

def raw4761 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -2, 1], ![2, -2, 2, -2]]

theorem canonical4761 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4761 = injectiveMoment H node2279 := by
  rfl

def raw4762 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, 1, -1]]

def raw4762step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-2, 2, -1, 1]]

def raw4762step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical4762 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4762 = injectiveMoment H node1747 := by
  calc
    injectiveMoment H raw4762 = injectiveMoment H raw4762step0 := by
      have heq : raw4762step0 = -raw4762 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4762).symm
    injectiveMoment H raw4762step0 = injectiveMoment H raw4762step1 := by
      have heq : raw4762step1 = (fun i j => raw4762step0 (permutation142 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4762step0 permutation142 permutation12
    _ = injectiveMoment H node1747 := by rfl

def raw4763 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, -2, 1, -1]]

theorem canonical4763 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4763 = injectiveMoment H node2281 := by
  rfl

def raw4764 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, 0, 0]]

def raw4764step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 0, 1, -1], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-2, 2, 0, 0]]

def raw4764step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![0, -2, 2, 0], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical4764 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4764 = injectiveMoment H node1999 := by
  calc
    injectiveMoment H raw4764 = injectiveMoment H raw4764step0 := by
      have heq : raw4764step0 = -raw4764 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4764).symm
    injectiveMoment H raw4764step0 = injectiveMoment H raw4764step1 := by
      have heq : raw4764step1 = (fun i j => raw4764step0 (permutation142 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4764step0 permutation142 permutation12
    _ = injectiveMoment H node1999 := by rfl

def raw4765 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw4765step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, 3, -3], ![0, 1, -1, 0], ![1, -2, 0, 1]]

theorem canonical4765 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4765 = injectiveMoment H node2847 := by
  calc
    injectiveMoment H raw4765 = injectiveMoment H raw4765step0 := by
      have heq : raw4765step0 = (fun i j => raw4765 (permutation113 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4765 permutation113 permutation15
    _ = injectiveMoment H node2847 := by rfl

def raw4766 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -2, 0, 1], ![1, 0, 3, -4]]

theorem canonical4766 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4766 = injectiveMoment H node2283 := by
  rfl

def raw4767 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, -1, 3, -3]]

theorem canonical4767 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4767 = injectiveMoment H node2284 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
