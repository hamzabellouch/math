import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw4672 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, -1, -1, 1]]

def raw4672step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, -1, -1, 1], ![1, 0, -1, 0]]

theorem canonical4672 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4672 = injectiveMoment H node2252 := by
  calc
    injectiveMoment H raw4672 = injectiveMoment H raw4672step0 := by
      have heq : raw4672step0 = (fun i j => raw4672 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4672 permutation34 permutation9
    _ = injectiveMoment H node2252 := by rfl

def raw4673 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![0, 1, 3, -4], ![2, -1, -2, 1]]

def raw4673step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, -1, 1, -1], ![0, -1, 3, -2], ![1, 2, -4, 1]]

def raw4673step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 1, -1, 1], ![0, 1, -3, 2], ![-1, -2, 4, -1]]

def raw4673step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, 2, -2, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

theorem canonical4673 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4673 = injectiveMoment H node468 := by
  calc
    injectiveMoment H raw4673 = injectiveMoment H raw4673step0 := by
      have heq : raw4673step0 = raw4673.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4673).symm
    injectiveMoment H raw4673step0 = injectiveMoment H raw4673step1 := by
      have heq : raw4673step1 = -raw4673step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4673step0).symm
    injectiveMoment H raw4673step1 = injectiveMoment H raw4673step2 := by
      have heq : raw4673step2 = (fun i j => raw4673step1 (permutation27 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4673step1 permutation27 permutation16
    _ = injectiveMoment H node468 := by rfl

def raw4674 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw4674step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 1, -2], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw4674step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical4674 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4674 = injectiveMoment H node454 := by
  calc
    injectiveMoment H raw4674 = injectiveMoment H raw4674step0 := by
      have heq : raw4674step0 = -raw4674 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4674).symm
    injectiveMoment H raw4674step0 = injectiveMoment H raw4674step1 := by
      have heq : raw4674step1 = (fun i j => raw4674step0 (permutation28 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4674step0 permutation28 permutation23
    _ = injectiveMoment H node454 := by rfl

def raw4675 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, -1, 0, 0], ![1, 1, 1, -3]]

def raw4675step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 1, -2], ![-1, 1, 0, 0], ![-1, -1, -1, 3]]

def raw4675step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 1, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical4675 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4675 = injectiveMoment H node939 := by
  calc
    injectiveMoment H raw4675 = injectiveMoment H raw4675step0 := by
      have heq : raw4675step0 = -raw4675 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4675).symm
    injectiveMoment H raw4675step0 = injectiveMoment H raw4675step1 := by
      have heq : raw4675step1 = (fun i j => raw4675step0 (permutation31 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4675step0 permutation31 permutation21
    _ = injectiveMoment H node939 := by rfl

def raw4676 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, -1, 3, -3], ![1, 1, -2, 0]]

def raw4676step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, -1, 3, -2], ![1, 2, -3, 0]]

def raw4676step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![0, 1, -3, 2], ![-1, -2, 3, 0]]

def raw4676step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

theorem canonical4676 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4676 = injectiveMoment H node495 := by
  calc
    injectiveMoment H raw4676 = injectiveMoment H raw4676step0 := by
      have heq : raw4676step0 = raw4676.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4676).symm
    injectiveMoment H raw4676step0 = injectiveMoment H raw4676step1 := by
      have heq : raw4676step1 = -raw4676step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4676step0).symm
    injectiveMoment H raw4676step1 = injectiveMoment H raw4676step2 := by
      have heq : raw4676step2 = (fun i j => raw4676step1 (permutation27 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4676step1 permutation27 permutation16
    _ = injectiveMoment H node495 := by rfl

def raw4677 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, 0, -2, 1], ![1, 0, 3, -4]]

def raw4677step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical4677 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4677 = injectiveMoment H node1278 := by
  calc
    injectiveMoment H raw4677 = injectiveMoment H raw4677step0 := by
      have heq : raw4677step0 = (fun i j => raw4677 (permutation18 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4677 permutation18 permutation15
    _ = injectiveMoment H node1278 := by rfl

def raw4678 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, 0, 2, -3], ![1, 0, -1, 0]]

def raw4678step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical4678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4678 = injectiveMoment H node1003 := by
  calc
    injectiveMoment H raw4678 = injectiveMoment H raw4678step0 := by
      have heq : raw4678step0 = (fun i j => raw4678 (permutation20 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4678 permutation20 permutation17
    _ = injectiveMoment H node1003 := by rfl

def raw4679 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, 0, 3, -4], ![1, 0, -2, 1]]

def raw4679step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -2, 0, 1]]

theorem canonical4679 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4679 = injectiveMoment H node1278 := by
  calc
    injectiveMoment H raw4679 = injectiveMoment H raw4679step0 := by
      have heq : raw4679step0 = (fun i j => raw4679 (permutation20 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4679 permutation20 permutation15
    _ = injectiveMoment H node1278 := by rfl

def raw4680 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, -1, 2], ![1, 1, 2, -4], ![1, -1, -1, 1]]

def raw4680step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 1, -2], ![-1, -1, -2, 4], ![-1, 1, 1, -1]]

def raw4680step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

theorem canonical4680 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4680 = injectiveMoment H node454 := by
  calc
    injectiveMoment H raw4680 = injectiveMoment H raw4680step0 := by
      have heq : raw4680step0 = -raw4680 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4680).symm
    injectiveMoment H raw4680step0 = injectiveMoment H raw4680step1 := by
      have heq : raw4680step1 = (fun i j => raw4680step0 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4680step0 permutation22 permutation23
    _ = injectiveMoment H node454 := by rfl

def raw4681 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 1, 2, -4]]

def raw4681step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, 0, -1], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, -1, -2, 4]]

def raw4681step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, -1, 4], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical4681 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4681 = injectiveMoment H node1576 := by
  calc
    injectiveMoment H raw4681 = injectiveMoment H raw4681step0 := by
      have heq : raw4681step0 = -raw4681 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4681).symm
    injectiveMoment H raw4681step0 = injectiveMoment H raw4681step1 := by
      have heq : raw4681step1 = (fun i j => raw4681step0 (permutation128 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4681step0 permutation128 permutation23
    _ = injectiveMoment H node1576 := by rfl

def raw4682 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 0, 1], ![1, -1, -2, 2], ![1, 1, 2, -4]]

def raw4682step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, 0, -2, 2], ![1, 1, 2, -4]]

def raw4682step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![0, 0, 2, -2], ![-1, -1, -2, 4]]

def raw4682step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical4682 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4682 = injectiveMoment H node917 := by
  calc
    injectiveMoment H raw4682 = injectiveMoment H raw4682step0 := by
      have heq : raw4682step0 = raw4682.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4682).symm
    injectiveMoment H raw4682step0 = injectiveMoment H raw4682step1 := by
      have heq : raw4682step1 = -raw4682step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4682step0).symm
    injectiveMoment H raw4682step1 = injectiveMoment H raw4682step2 := by
      have heq : raw4682step2 = (fun i j => raw4682step1 (permutation31 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4682step1 permutation31 permutation15
    _ = injectiveMoment H node917 := by rfl

def raw4683 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 1, 0], ![1, -1, -2, 2], ![1, 1, 1, -3]]

def raw4683step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, 1, -2, 1], ![1, 0, 2, -3]]

def raw4683step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![0, -1, 2, -1], ![-1, 0, -2, 3]]

def raw4683step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 3, -2], ![0, 2, -1, -1], ![1, -1, -1, 1]]

theorem canonical4683 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4683 = injectiveMoment H node1249 := by
  calc
    injectiveMoment H raw4683 = injectiveMoment H raw4683step0 := by
      have heq : raw4683step0 = raw4683.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4683).symm
    injectiveMoment H raw4683step0 = injectiveMoment H raw4683step1 := by
      have heq : raw4683step1 = -raw4683step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4683step0).symm
    injectiveMoment H raw4683step1 = injectiveMoment H raw4683step2 := by
      have heq : raw4683step2 = (fun i j => raw4683step1 (permutation25 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4683step1 permutation25 permutation16
    _ = injectiveMoment H node1249 := by rfl

def raw4684 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 1, 0], ![1, -1, 2, -2], ![1, 1, -3, 1]]

def raw4684step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

def raw4684step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![0, -1, -2, 3], ![-1, 0, 2, -1]]

def raw4684step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical4684 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4684 = injectiveMoment H node1208 := by
  calc
    injectiveMoment H raw4684 = injectiveMoment H raw4684step0 := by
      have heq : raw4684step0 = raw4684.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4684).symm
    injectiveMoment H raw4684step0 = injectiveMoment H raw4684step1 := by
      have heq : raw4684step1 = -raw4684step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4684step0).symm
    injectiveMoment H raw4684step1 = injectiveMoment H raw4684step2 := by
      have heq : raw4684step2 = (fun i j => raw4684step1 (permutation25 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4684step1 permutation25 permutation15
    _ = injectiveMoment H node1208 := by rfl

def raw4685 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw4685step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -2, 1, 1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical4685 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4685 = injectiveMoment H node2055 := by
  calc
    injectiveMoment H raw4685 = injectiveMoment H raw4685step0 := by
      have heq : raw4685step0 = (fun i j => raw4685 (permutation83 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4685 permutation83 permutation21
    _ = injectiveMoment H node2055 := by rfl

def raw4686 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw4686step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical4686 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4686 = injectiveMoment H node2076 := by
  calc
    injectiveMoment H raw4686 = injectiveMoment H raw4686step0 := by
      have heq : raw4686step0 = (fun i j => raw4686 (permutation39 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4686 permutation39 permutation12
    _ = injectiveMoment H node2076 := by rfl

def raw4687 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw4687step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 0, 0], ![1, -1, 1, -1]]

theorem canonical4687 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4687 = injectiveMoment H node2085 := by
  calc
    injectiveMoment H raw4687 = injectiveMoment H raw4687step0 := by
      have heq : raw4687step0 = (fun i j => raw4687 (permutation40 i) (permutation12 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4687 permutation40 permutation12
    _ = injectiveMoment H node2085 := by rfl

def raw4688 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -2, 1]]

def raw4688step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, 0, -1], ![0, 1, -2, 1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 2, -1]]

def raw4688step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, -1, 0, 1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, -1, -1, 0]]

theorem canonical4688 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4688 = injectiveMoment H node2065 := by
  calc
    injectiveMoment H raw4688 = injectiveMoment H raw4688step0 := by
      have heq : raw4688step0 = -raw4688 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4688).symm
    injectiveMoment H raw4688step0 = injectiveMoment H raw4688step1 := by
      have heq : raw4688step1 = (fun i j => raw4688step0 (permutation70 i) (permutation22 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4688step0 permutation70 permutation22
    _ = injectiveMoment H node2065 := by rfl

def raw4689 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![1, -1, -3, 3], ![1, 1, 1, -3]]

def raw4689step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, -1, -1, 1], ![0, 2, -3, 1], ![1, -1, 3, -3]]

def raw4689step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 1, 1, -1], ![0, -2, 3, -1], ![-1, 1, -3, 3]]

def raw4689step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -1, 3], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 3, -3]]

theorem canonical4689 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4689 = injectiveMoment H node604 := by
  calc
    injectiveMoment H raw4689 = injectiveMoment H raw4689step0 := by
      have heq : raw4689step0 = raw4689.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4689).symm
    injectiveMoment H raw4689step0 = injectiveMoment H raw4689step1 := by
      have heq : raw4689step1 = -raw4689step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4689step0).symm
    injectiveMoment H raw4689step1 = injectiveMoment H raw4689step2 := by
      have heq : raw4689step2 = (fun i j => raw4689step1 (permutation21 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4689step1 permutation21 permutation16
    _ = injectiveMoment H node604 := by rfl

def raw4690 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![1, -1, -2, 2], ![1, 1, 0, -2]]

def raw4690step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 0, -1]]

theorem canonical4690 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4690 = injectiveMoment H node510 := by
  calc
    injectiveMoment H raw4690 = injectiveMoment H raw4690step0 := by
      have heq : raw4690step0 = (fun i j => raw4690 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4690 permutation22 permutation23
    _ = injectiveMoment H node510 := by rfl

def raw4691 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![1, -1, -1, 1], ![1, 1, -1, -1]]

def raw4691step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![0, 2, -1, -1], ![1, -1, -1, 1], ![1, -1, 1, -1]]

theorem canonical4691 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4691 = injectiveMoment H node621 := by
  calc
    injectiveMoment H raw4691 = injectiveMoment H raw4691step0 := by
      have heq : raw4691step0 = (fun i j => raw4691 (permutation9 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4691 permutation9 permutation11
    _ = injectiveMoment H node621 := by rfl

def raw4692 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 2, -1], ![1, -1, 0, 0], ![1, 1, -2, 0]]

def raw4692step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical4692 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4692 = injectiveMoment H node1000 := by
  calc
    injectiveMoment H raw4692 = injectiveMoment H raw4692step0 := by
      have heq : raw4692step0 = (fun i j => raw4692 (permutation18 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4692 permutation18 permutation29
    _ = injectiveMoment H node1000 := by rfl

def raw4693 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

theorem canonical4693 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4693 = injectiveMoment H node2261 := by
  rfl

def raw4694 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw4694step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 1, 0]]

theorem canonical4694 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4694 = injectiveMoment H node2710 := by
  calc
    injectiveMoment H raw4694 = injectiveMoment H raw4694step0 := by
      have heq : raw4694step0 = (fun i j => raw4694 (permutation67 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4694 permutation67 permutation16
    _ = injectiveMoment H node2710 := by rfl

def raw4695 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw4695step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, -2, 1, 0]]

theorem canonical4695 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4695 = injectiveMoment H node2710 := by
  calc
    injectiveMoment H raw4695 = injectiveMoment H raw4695step0 := by
      have heq : raw4695step0 = (fun i j => raw4695 (permutation65 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4695 permutation65 permutation16
    _ = injectiveMoment H node2710 := by rfl

def raw4696 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 0, -2, 2], ![2, 0, -1, -1]]

def raw4696step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, -2, 1, 0]]

theorem canonical4696 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4696 = injectiveMoment H node1223 := by
  calc
    injectiveMoment H raw4696 = injectiveMoment H raw4696step0 := by
      have heq : raw4696step0 = (fun i j => raw4696 (permutation18 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4696 permutation18 permutation16
    _ = injectiveMoment H node1223 := by rfl

def raw4697 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -3, 2], ![1, -1, 0, 0], ![1, 0, 0, -1]]

theorem canonical4697 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4697 = injectiveMoment H node2262 := by
  rfl

def raw4698 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -3, 2], ![2, -1, 0, -1]]

theorem canonical4698 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4698 = injectiveMoment H node689 := by
  rfl

def raw4699 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

theorem canonical4699 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4699 = injectiveMoment H node2263 := by
  rfl

def raw4700 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw4700step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical4700 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4700 = injectiveMoment H node1636 := by
  calc
    injectiveMoment H raw4700 = injectiveMoment H raw4700step0 := by
      have heq : raw4700step0 = (fun i j => raw4700 (permutation72 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4700 permutation72 permutation29
    _ = injectiveMoment H node1636 := by rfl

def raw4701 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -2, 1], ![2, -1, -1, 0]]

def raw4701step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 2, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical4701 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4701 = injectiveMoment H node476 := by
  calc
    injectiveMoment H raw4701 = injectiveMoment H raw4701step0 := by
      have heq : raw4701step0 = (fun i j => raw4701 (permutation19 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4701 permutation19 permutation29
    _ = injectiveMoment H node476 := by rfl

def raw4702 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, 0, 0, -1]]

theorem canonical4702 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4702 = injectiveMoment H node2264 := by
  rfl

def raw4703 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, -1, 3, -2], ![0, 1, -1, 0], ![1, -1, -1, 1], ![1, 0, -1, 0]]

def raw4703step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 1, -2, 0]]

theorem canonical4703 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4703 = injectiveMoment H node1685 := by
  calc
    injectiveMoment H raw4703 = injectiveMoment H raw4703step0 := by
      have heq : raw4703step0 = (fun i j => raw4703 (permutation77 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4703 permutation77 permutation29
    _ = injectiveMoment H node1685 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
