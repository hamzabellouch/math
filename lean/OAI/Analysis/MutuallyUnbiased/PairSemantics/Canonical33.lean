import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1056 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw1056step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, 0, -1, 1], ![0, -1, 1, 0], ![-1, 0, 0, 1], ![-1, -1, 0, 2]]

def raw1056step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical1056 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1056 = injectiveMoment H node2747 := by
  calc
    injectiveMoment H raw1056 = injectiveMoment H raw1056step0 := by
      have heq : raw1056step0 = -raw1056 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1056).symm
    injectiveMoment H raw1056step0 = injectiveMoment H raw1056step1 := by
      have heq : raw1056step1 = (fun i j => raw1056step0 (permutation78 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1056step0 permutation78 permutation21
    _ = injectiveMoment H node2747 := by rfl

def raw1057 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

theorem canonical1057 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1057 = injectiveMoment H node1470 := by
  rfl

def raw1058 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw1058step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![0, 1, -1, 0], ![4, -1, 0, -3]]

def raw1058step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical1058 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1058 = injectiveMoment H node1178 := by
  calc
    injectiveMoment H raw1058 = injectiveMoment H raw1058step0 := by
      have heq : raw1058step0 = raw1058.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1058).symm
    injectiveMoment H raw1058step0 = injectiveMoment H raw1058step1 := by
      have heq : raw1058step1 = (fun i j => raw1058step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1058step0 permutation27 permutation18
    _ = injectiveMoment H node1178 := by rfl

def raw1059 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1059step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-2, 0, 0, 2]]

def raw1059step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical1059 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1059 = injectiveMoment H node2739 := by
  calc
    injectiveMoment H raw1059 = injectiveMoment H raw1059step0 := by
      have heq : raw1059step0 = -raw1059 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1059).symm
    injectiveMoment H raw1059step0 = injectiveMoment H raw1059step1 := by
      have heq : raw1059step1 = (fun i j => raw1059step0 (permutation76 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1059step0 permutation76 permutation21
    _ = injectiveMoment H node2739 := by rfl

def raw1060 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1060step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, 0, -1, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-2, 0, 1, 1]]

def raw1060step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical1060 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1060 = injectiveMoment H node2749 := by
  calc
    injectiveMoment H raw1060 = injectiveMoment H raw1060step0 := by
      have heq : raw1060step0 = -raw1060 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1060).symm
    injectiveMoment H raw1060step0 = injectiveMoment H raw1060step1 := by
      have heq : raw1060step1 = (fun i j => raw1060step0 (permutation64 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1060step0 permutation64 permutation23
    _ = injectiveMoment H node2749 := by rfl

def raw1061 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

theorem canonical1061 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1061 = injectiveMoment H node1471 := by
  rfl

def raw1062 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1062step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, -1, 0, 2]]

def raw1062step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, -1, 2], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical1062 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1062 = injectiveMoment H node2747 := by
  calc
    injectiveMoment H raw1062 = injectiveMoment H raw1062step0 := by
      have heq : raw1062step0 = -raw1062 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1062).symm
    injectiveMoment H raw1062step0 = injectiveMoment H raw1062step1 := by
      have heq : raw1062step1 = (fun i j => raw1062step0 (permutation76 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1062step0 permutation76 permutation23
    _ = injectiveMoment H node2747 := by rfl

def raw1063 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1063step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, 0, -1, 1], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, -1, 1, 1]]

def raw1063step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, -1, 1]]

theorem canonical1063 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1063 = injectiveMoment H node2755 := by
  calc
    injectiveMoment H raw1063 = injectiveMoment H raw1063step0 := by
      have heq : raw1063step0 = -raw1063 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1063).symm
    injectiveMoment H raw1063step0 = injectiveMoment H raw1063step1 := by
      have heq : raw1063step1 = (fun i j => raw1063step0 (permutation70 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1063step0 permutation70 permutation21
    _ = injectiveMoment H node2755 := by rfl

def raw1064 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -2, 0]]

theorem canonical1064 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1064 = injectiveMoment H node1472 := by
  rfl

def raw1065 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw1065step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![0, 1, 0, -1], ![4, -1, -1, -2]]

def raw1065step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical1065 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1065 = injectiveMoment H node914 := by
  calc
    injectiveMoment H raw1065 = injectiveMoment H raw1065step0 := by
      have heq : raw1065step0 = raw1065.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1065).symm
    injectiveMoment H raw1065step0 = injectiveMoment H raw1065step1 := by
      have heq : raw1065step1 = (fun i j => raw1065step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1065step0 permutation28 permutation24
    _ = injectiveMoment H node914 := by rfl

def raw1066 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw1066step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

theorem canonical1066 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1066 = injectiveMoment H node1471 := by
  calc
    injectiveMoment H raw1066 = injectiveMoment H raw1066step0 := by
      have heq : raw1066step0 = (fun i j => raw1066 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1066 permutation35 permutation9
    _ = injectiveMoment H node1471 := by rfl

def raw1067 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -2, -1]]

def raw1067step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![0, 1, 1, -2], ![4, -1, -2, -1]]

def raw1067step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -2, 0]]

theorem canonical1067 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1067 = injectiveMoment H node772 := by
  calc
    injectiveMoment H raw1067 = injectiveMoment H raw1067step0 := by
      have heq : raw1067step0 = raw1067.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1067).symm
    injectiveMoment H raw1067step0 = injectiveMoment H raw1067step1 := by
      have heq : raw1067step1 = (fun i j => raw1067step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1067step0 permutation27 permutation18
    _ = injectiveMoment H node772 := by rfl

def raw1068 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1068step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -2, 0]]

theorem canonical1068 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1068 = injectiveMoment H node1471 := by
  calc
    injectiveMoment H raw1068 = injectiveMoment H raw1068step0 := by
      have heq : raw1068step0 = (fun i j => raw1068 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1068 permutation36 permutation15
    _ = injectiveMoment H node1471 := by rfl

def raw1069 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 1, -3]]

def raw1069step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![0, 1, -2, 1], ![4, -1, 0, -3]]

def raw1069step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -2, 1, 0]]

theorem canonical1069 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1069 = injectiveMoment H node1180 := by
  calc
    injectiveMoment H raw1069 = injectiveMoment H raw1069step0 := by
      have heq : raw1069step0 = raw1069.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1069).symm
    injectiveMoment H raw1069step0 = injectiveMoment H raw1069step1 := by
      have heq : raw1069step1 = (fun i j => raw1069step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1069step0 permutation27 permutation18
    _ = injectiveMoment H node1180 := by rfl

def raw1070 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1070step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem canonical1070 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1070 = injectiveMoment H node1468 := by
  calc
    injectiveMoment H raw1070 = injectiveMoment H raw1070step0 := by
      have heq : raw1070step0 = (fun i j => raw1070 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1070 permutation36 permutation15
    _ = injectiveMoment H node1468 := by rfl

def raw1071 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1071step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, 0, -1, 1], ![0, -2, 1, 1], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw1071step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, -1, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

theorem canonical1071 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1071 = injectiveMoment H node2749 := by
  calc
    injectiveMoment H raw1071 = injectiveMoment H raw1071step0 := by
      have heq : raw1071step0 = -raw1071 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1071).symm
    injectiveMoment H raw1071step0 = injectiveMoment H raw1071step1 := by
      have heq : raw1071step1 = (fun i j => raw1071step0 (permutation72 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1071step0 permutation72 permutation21
    _ = injectiveMoment H node2749 := by rfl

def raw1072 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, 0, -2]]

def raw1072step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![0, 1, -1, 0], ![4, -1, -1, -2]]

def raw1072step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical1072 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1072 = injectiveMoment H node775 := by
  calc
    injectiveMoment H raw1072 = injectiveMoment H raw1072step0 := by
      have heq : raw1072step0 = raw1072.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1072).symm
    injectiveMoment H raw1072step0 = injectiveMoment H raw1072step1 := by
      have heq : raw1072step1 = (fun i j => raw1072step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1072step0 permutation29 permutation20
    _ = injectiveMoment H node775 := by rfl

def raw1073 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1073step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, 0, -1, 1], ![0, -2, 0, 2], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw1073step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical1073 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1073 = injectiveMoment H node2739 := by
  calc
    injectiveMoment H raw1073 = injectiveMoment H raw1073step0 := by
      have heq : raw1073step0 = -raw1073 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1073).symm
    injectiveMoment H raw1073step0 = injectiveMoment H raw1073step1 := by
      have heq : raw1073step1 = (fun i j => raw1073step0 (permutation66 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1073step0 permutation66 permutation23
    _ = injectiveMoment H node2739 := by rfl

def raw1074 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw1074step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![0, 1, 0, -1], ![4, -1, -2, -1]]

def raw1074step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical1074 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1074 = injectiveMoment H node775 := by
  calc
    injectiveMoment H raw1074 = injectiveMoment H raw1074step0 := by
      have heq : raw1074step0 = raw1074.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1074).symm
    injectiveMoment H raw1074step0 = injectiveMoment H raw1074step1 := by
      have heq : raw1074step1 = (fun i j => raw1074step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1074step0 permutation27 permutation18
    _ = injectiveMoment H node775 := by rfl

def raw1075 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1075step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

theorem canonical1075 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1075 = injectiveMoment H node1467 := by
  calc
    injectiveMoment H raw1075 = injectiveMoment H raw1075step0 := by
      have heq : raw1075step0 = (fun i j => raw1075 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1075 permutation36 permutation15
    _ = injectiveMoment H node1467 := by rfl

def raw1076 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def raw1076step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 0, 2], ![0, 1, -1, 0], ![4, -1, 0, -3]]

def raw1076step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical1076 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1076 = injectiveMoment H node1178 := by
  calc
    injectiveMoment H raw1076 = injectiveMoment H raw1076step0 := by
      have heq : raw1076step0 = raw1076.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1076).symm
    injectiveMoment H raw1076step0 = injectiveMoment H raw1076step1 := by
      have heq : raw1076step1 = (fun i j => raw1076step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1076step0 permutation29 permutation18
    _ = injectiveMoment H node1178 := by rfl

def raw1077 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw1077step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 0, 2], ![0, 1, 0, -1], ![4, -1, -1, -2]]

def raw1077step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -2, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical1077 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1077 = injectiveMoment H node914 := by
  calc
    injectiveMoment H raw1077 = injectiveMoment H raw1077step0 := by
      have heq : raw1077step0 = raw1077.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1077).symm
    injectiveMoment H raw1077step0 = injectiveMoment H raw1077step1 := by
      have heq : raw1077step1 = (fun i j => raw1077step0 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1077step0 permutation30 permutation24
    _ = injectiveMoment H node914 := by rfl

def raw1078 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 1, -3]]

def raw1078step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 1, 1], ![0, 1, -2, 1], ![4, -1, 0, -3]]

def raw1078step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, -2, 1, 0]]

theorem canonical1078 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1078 = injectiveMoment H node1186 := by
  calc
    injectiveMoment H raw1078 = injectiveMoment H raw1078step0 := by
      have heq : raw1078step0 = raw1078.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1078).symm
    injectiveMoment H raw1078step0 = injectiveMoment H raw1078step1 := by
      have heq : raw1078step1 = (fun i j => raw1078step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1078step0 permutation27 permutation18
    _ = injectiveMoment H node1186 := by rfl

def raw1079 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 1, -1], ![1, 1, -1, -1], ![1, 1, 0, -2]]

def raw1079step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 1, 1], ![0, 1, -1, 0], ![4, -1, -1, -2]]

def raw1079step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical1079 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1079 = injectiveMoment H node787 := by
  calc
    injectiveMoment H raw1079 = injectiveMoment H raw1079step0 := by
      have heq : raw1079step0 = raw1079.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1079).symm
    injectiveMoment H raw1079step0 = injectiveMoment H raw1079step1 := by
      have heq : raw1079step1 = (fun i j => raw1079step0 (permutation27 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1079step0 permutation27 permutation20
    _ = injectiveMoment H node787 := by rfl

def raw1080 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical1080 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1080 = injectiveMoment H node1473 := by
  rfl

def raw1081 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical1081 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1081 = injectiveMoment H node1474 := by
  rfl

def raw1082 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -2, 1], ![2, 1, 0, -3]]

theorem canonical1082 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1082 = injectiveMoment H node394 := by
  rfl

def raw1083 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical1083 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1083 = injectiveMoment H node1475 := by
  rfl

def raw1084 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical1084 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1084 = injectiveMoment H node1476 := by
  rfl

def raw1085 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 0, -2]]

theorem canonical1085 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1085 = injectiveMoment H node1477 := by
  rfl

def raw1086 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical1086 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1086 = injectiveMoment H node1478 := by
  rfl

def raw1087 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw1087step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical1087 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1087 = injectiveMoment H node1478 := by
  calc
    injectiveMoment H raw1087 = injectiveMoment H raw1087step0 := by
      have heq : raw1087step0 = (fun i j => raw1087 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1087 permutation34 permutation9
    _ = injectiveMoment H node1478 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
