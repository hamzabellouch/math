import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw5024 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, -1, 2], ![1, 1, 2, -4]]

def raw5024step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, -1, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -2, 1, 0], ![1, 1, 2, -4]]

theorem canonical5024 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5024 = injectiveMoment H node2220 := by
  calc
    injectiveMoment H raw5024 = injectiveMoment H raw5024step0 := by
      have heq : raw5024step0 = (fun i j => raw5024 (permutation112 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5024 permutation112 permutation15
    _ = injectiveMoment H node2220 := by rfl

def raw5025 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 2, -3]]

def raw5025step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 1, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical5025 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5025 = injectiveMoment H node2844 := by
  calc
    injectiveMoment H raw5025 = injectiveMoment H raw5025step0 := by
      have heq : raw5025step0 = (fun i j => raw5025 (permutation113 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5025 permutation113 permutation15
    _ = injectiveMoment H node2844 := by rfl

def raw5026 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -1, 1], ![1, -2, -1, 2], ![1, 1, 1, -3]]

def raw5026step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![1, -1, -1, 1], ![0, 1, 2, -3]]

def raw5026step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![-1, 1, 1, -1], ![0, -1, -2, 3]]

def raw5026step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 2, -1, -1], ![1, -1, 1, -1]]

theorem canonical5026 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5026 = injectiveMoment H node1208 := by
  calc
    injectiveMoment H raw5026 = injectiveMoment H raw5026step0 := by
      have heq : raw5026step0 = raw5026.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5026).symm
    injectiveMoment H raw5026step0 = injectiveMoment H raw5026step1 := by
      have heq : raw5026step1 = -raw5026step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5026step0).symm
    injectiveMoment H raw5026step1 = injectiveMoment H raw5026step2 := by
      have heq : raw5026step2 = (fun i j => raw5026step1 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5026step1 permutation29 permutation15
    _ = injectiveMoment H node1208 := by rfl

def raw5027 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, -1, 1], ![1, -1, -1, 1], ![1, 0, 1, -2]]

def raw5027step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, -1, 0], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![-1, 0, -1, 2]]

def raw5027step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 1, -1, -1]]

theorem canonical5027 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5027 = injectiveMoment H node1006 := by
  calc
    injectiveMoment H raw5027 = injectiveMoment H raw5027step0 := by
      have heq : raw5027step0 = -raw5027 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5027).symm
    injectiveMoment H raw5027step0 = injectiveMoment H raw5027step1 := by
      have heq : raw5027step1 = (fun i j => raw5027step0 (permutation13 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5027step0 permutation13 permutation18
    _ = injectiveMoment H node1006 := by rfl

def raw5028 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def raw5028step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, -1, 0], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-2, 2, 2, -2]]

def raw5028step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 2, 2], ![0, 0, -1, 1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical5028 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5028 = injectiveMoment H node1521 := by
  calc
    injectiveMoment H raw5028 = injectiveMoment H raw5028step0 := by
      have heq : raw5028step0 = -raw5028 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5028).symm
    injectiveMoment H raw5028step0 = injectiveMoment H raw5028step1 := by
      have heq : raw5028step1 = (fun i j => raw5028step0 (permutation148 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5028step0 permutation148 permutation13
    _ = injectiveMoment H node1521 := by rfl

def raw5029 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def raw5029step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 1, -1, 0], ![2, -2, 3, -3]]

theorem canonical5029 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5029 = injectiveMoment H node2277 := by
  calc
    injectiveMoment H raw5029 = injectiveMoment H raw5029step0 := by
      have heq : raw5029step0 = (fun i j => raw5029 (permutation33 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5029 permutation33 permutation10
    _ = injectiveMoment H node2277 := by rfl

def raw5030 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 1, -1]]

def raw5030step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, -1, 0], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 1, 2, -2], ![-1, 1, -1, 1]]

def raw5030step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, 0, -1, 1], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical5030 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5030 = injectiveMoment H node1774 := by
  calc
    injectiveMoment H raw5030 = injectiveMoment H raw5030step0 := by
      have heq : raw5030step0 = -raw5030 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5030).symm
    injectiveMoment H raw5030step0 = injectiveMoment H raw5030step1 := by
      have heq : raw5030step1 = (fun i j => raw5030step0 (permutation117 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5030step0 permutation117 permutation27
    _ = injectiveMoment H node1774 := by rfl

def raw5031 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, -2, -3, 3]]

def raw5031step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![1, 1, 1, -3], ![0, -1, -2, 3]]

def raw5031step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![1, 1, 1, -3]]

theorem canonical5031 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5031 = injectiveMoment H node790 := by
  calc
    injectiveMoment H raw5031 = injectiveMoment H raw5031step0 := by
      have heq : raw5031step0 = raw5031.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5031).symm
    injectiveMoment H raw5031step0 = injectiveMoment H raw5031step1 := by
      have heq : raw5031step1 = (fun i j => raw5031step0 (permutation27 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5031step0 permutation27 permutation17
    _ = injectiveMoment H node790 := by rfl

def raw5032 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 1, -1], ![1, -2, -3, 4], ![1, 1, 1, -3]]

def raw5032step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![1, 1, -3, 1], ![0, -1, 4, -3]]

def raw5032step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, 0, 2, -1], ![-1, -1, 3, -1], ![0, 1, -4, 3]]

def raw5032step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, 0, 3, -4]]

theorem canonical5032 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5032 = injectiveMoment H node932 := by
  calc
    injectiveMoment H raw5032 = injectiveMoment H raw5032step0 := by
      have heq : raw5032step0 = raw5032.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5032).symm
    injectiveMoment H raw5032step0 = injectiveMoment H raw5032step1 := by
      have heq : raw5032step1 = -raw5032step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5032step0).symm
    injectiveMoment H raw5032step1 = injectiveMoment H raw5032step2 := by
      have heq : raw5032step2 = (fun i j => raw5032step1 (permutation23 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5032step1 permutation23 permutation16
    _ = injectiveMoment H node932 := by rfl

def raw5033 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 1, -1], ![1, -1, -3, 3], ![1, 0, 1, -2]]

def raw5033step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![1, 1, -3, 1], ![0, -1, 3, -2]]

def raw5033step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -2, 1], ![1, 1, 1, -3]]

theorem canonical5033 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5033 = injectiveMoment H node800 := by
  calc
    injectiveMoment H raw5033 = injectiveMoment H raw5033step0 := by
      have heq : raw5033step0 = raw5033.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5033).symm
    injectiveMoment H raw5033step0 = injectiveMoment H raw5033step1 := by
      have heq : raw5033step1 = (fun i j => raw5033step0 (permutation29 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5033step0 permutation29 permutation19
    _ = injectiveMoment H node800 := by rfl

def raw5034 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 0, 0]]

def raw5034step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, -1, -1, 0], ![0, 0, -2, 2], ![0, -1, 1, 0], ![-1, 1, 2, -2], ![-1, 1, 0, 0]]

def raw5034step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 1, 2], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem canonical5034 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5034 = injectiveMoment H node1742 := by
  calc
    injectiveMoment H raw5034 = injectiveMoment H raw5034step0 := by
      have heq : raw5034step0 = -raw5034 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5034).symm
    injectiveMoment H raw5034step0 = injectiveMoment H raw5034step1 := by
      have heq : raw5034step1 = (fun i j => raw5034step0 (permutation126 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5034step0 permutation126 permutation27
    _ = injectiveMoment H node1742 := by rfl

def raw5035 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, -2, -2, 2]]

def raw5035step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![1, 2, -1, -2], ![0, -2, 0, 2]]

def raw5035step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![-1, 0, -1, 2], ![-1, -2, 1, 2], ![0, 2, 0, -2]]

def raw5035step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -2, 2]]

theorem canonical5035 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5035 = injectiveMoment H node1059 := by
  calc
    injectiveMoment H raw5035 = injectiveMoment H raw5035step0 := by
      have heq : raw5035step0 = raw5035.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5035).symm
    injectiveMoment H raw5035step0 = injectiveMoment H raw5035step1 := by
      have heq : raw5035step1 = -raw5035step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5035step0).symm
    injectiveMoment H raw5035step1 = injectiveMoment H raw5035step2 := by
      have heq : raw5035step2 = (fun i j => raw5035step1 (permutation19 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5035step1 permutation19 permutation21
    _ = injectiveMoment H node1059 := by rfl

def raw5036 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, -2, -3, 3]]

def raw5036step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![1, 0, 1, -2], ![1, 2, 0, -3], ![0, -2, -1, 3]]

def raw5036step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, 0, 1, -2]]

theorem canonical5036 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5036 = injectiveMoment H node794 := by
  calc
    injectiveMoment H raw5036 = injectiveMoment H raw5036step0 := by
      have heq : raw5036step0 = raw5036.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5036).symm
    injectiveMoment H raw5036step0 = injectiveMoment H raw5036step1 := by
      have heq : raw5036step1 = (fun i j => raw5036step0 (permutation28 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5036step0 permutation28 permutation23
    _ = injectiveMoment H node794 := by rfl

def raw5037 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 2, -2], ![1, -2, -3, 4], ![1, 1, 0, -2]]

def raw5037step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -2, 1], ![1, 2, -3, 0], ![0, -2, 4, -2]]

def raw5037step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 1, -3]]

theorem canonical5037 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5037 = injectiveMoment H node400 := by
  calc
    injectiveMoment H raw5037 = injectiveMoment H raw5037step0 := by
      have heq : raw5037step0 = raw5037.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5037).symm
    injectiveMoment H raw5037step0 = injectiveMoment H raw5037step1 := by
      have heq : raw5037step1 = (fun i j => raw5037step0 (permutation27 i) (permutation19 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5037step0 permutation27 permutation19
    _ = injectiveMoment H node400 := by rfl

def raw5038 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 0, 2, -2], ![1, -1, -3, 3], ![1, 0, 0, -1]]

def raw5038step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 0, -1, 0], ![1, 2, -3, 0], ![0, -2, 3, -1]]

def raw5038step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -2, 1]]

theorem canonical5038 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5038 = injectiveMoment H node803 := by
  calc
    injectiveMoment H raw5038 = injectiveMoment H raw5038step0 := by
      have heq : raw5038step0 = raw5038.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5038).symm
    injectiveMoment H raw5038step0 = injectiveMoment H raw5038step1 := by
      have heq : raw5038step1 = (fun i j => raw5038step0 (permutation30 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5038step0 permutation30 permutation29
    _ = injectiveMoment H node803 := by rfl

def raw5039 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 1, -3, 2], ![1, -2, 2, -1], ![1, 0, 0, -1]]

def raw5039step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -2, 0], ![1, -3, 2, 0], ![0, 2, -1, -1]]

def raw5039step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -2, 1, 0]]

theorem canonical5039 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5039 = injectiveMoment H node1277 := by
  calc
    injectiveMoment H raw5039 = injectiveMoment H raw5039step0 := by
      have heq : raw5039step0 = raw5039.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5039).symm
    injectiveMoment H raw5039step0 = injectiveMoment H raw5039step1 := by
      have heq : raw5039step1 = (fun i j => raw5039step0 (permutation30 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5039step0 permutation30 permutation28
    _ = injectiveMoment H node1277 := by rfl

def raw5040 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 1, -1, 0], ![1, -1, -2, 2], ![1, -1, 2, -2]]

def raw5040step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![1, 1, -1, -1], ![1, -1, -2, 2], ![0, 0, 2, -2]]

def raw5040step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![-1, -1, 1, 1], ![-1, 1, 2, -2], ![0, 0, -2, 2]]

def raw5040step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 2, -2]]

theorem canonical5040 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5040 = injectiveMoment H node1111 := by
  calc
    injectiveMoment H raw5040 = injectiveMoment H raw5040step0 := by
      have heq : raw5040step0 = raw5040.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5040).symm
    injectiveMoment H raw5040step0 = injectiveMoment H raw5040step1 := by
      have heq : raw5040step1 = -raw5040step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5040step0).symm
    injectiveMoment H raw5040step1 = injectiveMoment H raw5040step2 := by
      have heq : raw5040step2 = (fun i j => raw5040step1 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5040step1 permutation19 permutation15
    _ = injectiveMoment H node1111 := by rfl

def raw5041 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 1, 1, -2], ![2, -2, -2, 2]]

def raw5041step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![1, 1, -2], ![0, -2, 2]]

def raw5041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]

theorem canonical5041 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5041 = injectiveMoment H node202 := by
  calc
    injectiveMoment H raw5041 = injectiveMoment H raw5041step0 := by
      have heq : raw5041step0 = raw5041.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5041).symm
    injectiveMoment H raw5041step0 = injectiveMoment H raw5041step1 := by
      have heq : raw5041step1 = (fun i j => raw5041step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5041step0 permutation13 permutation3
    _ = injectiveMoment H node202 := by rfl

def raw5042 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![0, 1, 2, -3], ![2, -2, -3, 3]]

def raw5042step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![1, 2, -3], ![0, -3, 3]]

def raw5042step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -3, 3], ![1, 1, -2], ![1, 2, -3]]

theorem canonical5042 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5042 = injectiveMoment H node196 := by
  calc
    injectiveMoment H raw5042 = injectiveMoment H raw5042step0 := by
      have heq : raw5042step0 = raw5042.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5042).symm
    injectiveMoment H raw5042step0 = injectiveMoment H raw5042step1 := by
      have heq : raw5042step1 = (fun i j => raw5042step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5042step0 permutation13 permutation3
    _ = injectiveMoment H node196 := by rfl

def raw5043 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -4, 2, 1], ![1, 3, -3, -1]]

def raw5043step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -4, 3], ![1, 2, -3], ![0, 1, -1]]

def raw5043step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -3, 2], ![1, 3, -4]]

theorem canonical5043 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5043 = injectiveMoment H node228 := by
  calc
    injectiveMoment H raw5043 = injectiveMoment H raw5043step0 := by
      have heq : raw5043step0 = raw5043.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5043).symm
    injectiveMoment H raw5043step0 = injectiveMoment H raw5043step1 := by
      have heq : raw5043step1 = (fun i j => raw5043step0 (permutation14 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5043step0 permutation14 permutation4
    _ = injectiveMoment H node228 := by rfl

def raw5044 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -3, 1, 1], ![1, 2, -2, -1]]

def raw5044step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -3, 2], ![1, 1, -2], ![0, 1, -1]]

def raw5044step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]

theorem canonical5044 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5044 = injectiveMoment H node229 := by
  calc
    injectiveMoment H raw5044 = injectiveMoment H raw5044step0 := by
      have heq : raw5044step0 = raw5044.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5044).symm
    injectiveMoment H raw5044step0 = injectiveMoment H raw5044step1 := by
      have heq : raw5044step1 = (fun i j => raw5044step0 (permutation14 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5044step0 permutation14 permutation4
    _ = injectiveMoment H node229 := by rfl

def raw5045 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -2, -3, 4], ![0, 0, 2, -2], ![1, 1, 0, -2]]

def raw5045step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 0, 1], ![1, -3, 2, 0], ![0, 4, -2, -2]]

def raw5045step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 1, -3]]

theorem canonical5045 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5045 = injectiveMoment H node400 := by
  calc
    injectiveMoment H raw5045 = injectiveMoment H raw5045step0 := by
      have heq : raw5045step0 = raw5045.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5045).symm
    injectiveMoment H raw5045step0 = injectiveMoment H raw5045step1 := by
      have heq : raw5045step1 = (fun i j => raw5045step0 (permutation27 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5045step0 permutation27 permutation25
    _ = injectiveMoment H node400 := by rfl

def raw5046 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -2, -3, 4], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw5046step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![1, -3, 1, 1], ![0, 4, -2, -2]]

def raw5046step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 1, -3]]

theorem canonical5046 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5046 = injectiveMoment H node402 := by
  calc
    injectiveMoment H raw5046 = injectiveMoment H raw5046step0 := by
      have heq : raw5046step0 = raw5046.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5046).symm
    injectiveMoment H raw5046step0 = injectiveMoment H raw5046step1 := by
      have heq : raw5046step1 = (fun i j => raw5046step0 (permutation27 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5046step0 permutation27 permutation25
    _ = injectiveMoment H node402 := by rfl

def raw5047 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -2, -3, 4], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw5047step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 1, 0], ![1, -3, 2, 0], ![0, 4, -3, -1]]

def raw5047step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 2, -3], ![1, -2, 0, 1]]

theorem canonical5047 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5047 = injectiveMoment H node1187 := by
  calc
    injectiveMoment H raw5047 = injectiveMoment H raw5047step0 := by
      have heq : raw5047step0 = raw5047.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5047).symm
    injectiveMoment H raw5047step0 = injectiveMoment H raw5047step1 := by
      have heq : raw5047step1 = (fun i j => raw5047step0 (permutation30 i) (permutation28 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5047step0 permutation30 permutation28
    _ = injectiveMoment H node1187 := by rfl

def raw5048 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -2, -1, 2], ![0, 0, -2, 2], ![1, 1, 2, -4]]

def raw5048step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -2, 0, 1], ![1, -1, -2, 2], ![0, 2, 2, -4]]

def raw5048step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![-1, 2, 0, -1], ![-1, 1, 2, -2], ![0, -2, -2, 4]]

def raw5048step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, -1, 2, -1], ![0, 2, -1, -1], ![2, -1, 1, -2]]

theorem canonical5048 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5048 = injectiveMoment H node579 := by
  calc
    injectiveMoment H raw5048 = injectiveMoment H raw5048step0 := by
      have heq : raw5048step0 = raw5048.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5048).symm
    injectiveMoment H raw5048step0 = injectiveMoment H raw5048step1 := by
      have heq : raw5048step1 = -raw5048step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5048step0).symm
    injectiveMoment H raw5048step1 = injectiveMoment H raw5048step2 := by
      have heq : raw5048step2 = (fun i j => raw5048step1 (permutation29 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5048step1 permutation29 permutation21
    _ = injectiveMoment H node579 := by rfl

def raw5049 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -2, 3, -2], ![1, 1, -4, 2]]

def raw5049step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 3, -4], ![0, -2, 2]]

def raw5049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, -2, 1], ![1, 3, -4]]

theorem canonical5049 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5049 = injectiveMoment H node225 := by
  calc
    injectiveMoment H raw5049 = injectiveMoment H raw5049step0 := by
      have heq : raw5049step0 = raw5049.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5049).symm
    injectiveMoment H raw5049step0 = injectiveMoment H raw5049step1 := by
      have heq : raw5049step1 = (fun i j => raw5049step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5049step0 permutation13 permutation3
    _ = injectiveMoment H node225 := by rfl

def raw5050 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -1, -3, 3], ![0, 1, 1, -2], ![1, -1, 1, -1]]

def raw5050step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, 1, -1], ![1, -3, 1, 1], ![0, 3, -2, -1]]

def raw5050step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

theorem canonical5050 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5050 = injectiveMoment H node487 := by
  calc
    injectiveMoment H raw5050 = injectiveMoment H raw5050step0 := by
      have heq : raw5050step0 = raw5050.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5050).symm
    injectiveMoment H raw5050step0 = injectiveMoment H raw5050step1 := by
      have heq : raw5050step1 = (fun i j => raw5050step0 (permutation27 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5050step0 permutation27 permutation25
    _ = injectiveMoment H node487 := by rfl

def raw5051 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, -1, -2, 2], ![0, -1, -1, 2], ![1, 1, 2, -4]]

def raw5051step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![1, -1, -1, 1], ![1, -2, -1, 2], ![0, 2, 2, -4]]

def raw5051step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![-1, 1, 1, -1], ![-1, 2, 1, -2], ![0, -2, -2, 4]]

def raw5051step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, -2, 4], ![0, 2, -1, -1], ![1, -1, 1, -1], ![1, -1, 2, -2]]

theorem canonical5051 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5051 = injectiveMoment H node585 := by
  calc
    injectiveMoment H raw5051 = injectiveMoment H raw5051step0 := by
      have heq : raw5051step0 = raw5051.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5051).symm
    injectiveMoment H raw5051step0 = injectiveMoment H raw5051step1 := by
      have heq : raw5051step1 = -raw5051step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5051step0).symm
    injectiveMoment H raw5051step1 = injectiveMoment H raw5051step2 := by
      have heq : raw5051step2 = (fun i j => raw5051step1 (permutation27 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5051step1 permutation27 permutation21
    _ = injectiveMoment H node585 := by rfl

def raw5052 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![1, 1, 1, -3], ![1, -2, -2, 3]]

def raw5052step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 1, -2], ![1, 1, -2], ![0, -3, 3]]

def raw5052step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]

theorem canonical5052 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5052 = injectiveMoment H node223 := by
  calc
    injectiveMoment H raw5052 = injectiveMoment H raw5052step0 := by
      have heq : raw5052step0 = raw5052.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5052).symm
    injectiveMoment H raw5052step0 = injectiveMoment H raw5052step1 := by
      have heq : raw5052step1 = (fun i j => raw5052step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5052step0 permutation13 permutation3
    _ = injectiveMoment H node223 := by rfl

def raw5053 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -3, 2, 1], ![2, 2, -4, 0]]

def raw5053step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -3, 2], ![2, 2, -4], ![-1, 1, 0]]

def raw5053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]

theorem canonical5053 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5053 = injectiveMoment H node102 := by
  calc
    injectiveMoment H raw5053 = injectiveMoment H raw5053step0 := by
      have heq : raw5053step0 = raw5053.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5053).symm
    injectiveMoment H raw5053step0 = injectiveMoment H raw5053step1 := by
      have heq : raw5053step1 = (fun i j => raw5053step0 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5053step0 permutation16 permutation5
    _ = injectiveMoment H node102 := by rfl

def raw5054 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -2, 2, 0], ![2, 1, -4, 1]]

def raw5054step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![2, 2, -4], ![-1, 0, 1]]

def raw5054step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-2, -2, 4], ![1, 0, -1]]

def raw5054step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]

theorem canonical5054 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw5054 = injectiveMoment H node146 := by
  calc
    injectiveMoment H raw5054 = injectiveMoment H raw5054step0 := by
      have heq : raw5054step0 = raw5054.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw5054).symm
    injectiveMoment H raw5054step0 = injectiveMoment H raw5054step1 := by
      have heq : raw5054step1 = -raw5054step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw5054step0).symm
    injectiveMoment H raw5054step1 = injectiveMoment H raw5054step2 := by
      have heq : raw5054step2 = (fun i j => raw5054step1 (permutation25 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw5054step1 permutation25 permutation5
    _ = injectiveMoment H node146 := by rfl

def raw5055 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, 1, 2, -1], ![0, -1, -3, 4], ![0, 0, 1, -1], ![1, -1, 0, 0], ![1, 1, 0, -2]]

theorem canonical5055 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5055 = injectiveMoment H node2321 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
