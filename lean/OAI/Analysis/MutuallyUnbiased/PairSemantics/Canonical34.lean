import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1088 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 1, -1, -2]]

def raw1088step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![0, 2, -1, -1], ![4, -2, 0, -2]]

def raw1088step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, 0, -1, -1], ![0, -2, 1, 1], ![-4, 2, 0, 2]]

def raw1088step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

theorem canonical1088 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1088 = injectiveMoment H node1257 := by
  calc
    injectiveMoment H raw1088 = injectiveMoment H raw1088step0 := by
      have heq : raw1088step0 = raw1088.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1088).symm
    injectiveMoment H raw1088step0 = injectiveMoment H raw1088step1 := by
      have heq : raw1088step1 = -raw1088step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1088step0).symm
    injectiveMoment H raw1088step1 = injectiveMoment H raw1088step2 := by
      have heq : raw1088step2 = (fun i j => raw1088step1 (permutation16 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1088step1 permutation16 permutation24
    _ = injectiveMoment H node1257 := by rfl

def raw1089 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical1089 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1089 = injectiveMoment H node1479 := by
  rfl

def raw1090 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw1090step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical1090 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1090 = injectiveMoment H node1478 := by
  calc
    injectiveMoment H raw1090 = injectiveMoment H raw1090step0 := by
      have heq : raw1090step0 = (fun i j => raw1090 (permutation35 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1090 permutation35 permutation15
    _ = injectiveMoment H node1478 := by rfl

def raw1091 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -2, 0], ![1, 0, 0, -1]]

def raw1091step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -2, 0]]

theorem canonical1091 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1091 = injectiveMoment H node1480 := by
  calc
    injectiveMoment H raw1091 = injectiveMoment H raw1091step0 := by
      have heq : raw1091step0 = (fun i j => raw1091 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1091 permutation34 permutation9
    _ = injectiveMoment H node1480 := by rfl

def raw1092 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw1092step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![0, 2, 0, -2], ![4, -2, -1, -1]]

def raw1092step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical1092 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1092 = injectiveMoment H node773 := by
  calc
    injectiveMoment H raw1092 = injectiveMoment H raw1092step0 := by
      have heq : raw1092step0 = raw1092.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1092).symm
    injectiveMoment H raw1092step0 = injectiveMoment H raw1092step1 := by
      have heq : raw1092step1 = (fun i j => raw1092step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1092step0 permutation28 permutation24
    _ = injectiveMoment H node773 := by rfl

def raw1093 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1093step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical1093 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1093 = injectiveMoment H node1479 := by
  calc
    injectiveMoment H raw1093 = injectiveMoment H raw1093step0 := by
      have heq : raw1093step0 = (fun i j => raw1093 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1093 permutation36 permutation15
    _ = injectiveMoment H node1479 := by rfl

def raw1094 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem canonical1094 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1094 = injectiveMoment H node395 := by
  rfl

def raw1095 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1095step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical1095 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1095 = injectiveMoment H node1476 := by
  calc
    injectiveMoment H raw1095 = injectiveMoment H raw1095step0 := by
      have heq : raw1095step0 = (fun i j => raw1095 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1095 permutation36 permutation15
    _ = injectiveMoment H node1476 := by rfl

def raw1096 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, -1, -1]]

theorem canonical1096 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1096 = injectiveMoment H node396 := by
  rfl

def raw1097 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1097step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical1097 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1097 = injectiveMoment H node1475 := by
  calc
    injectiveMoment H raw1097 = injectiveMoment H raw1097step0 := by
      have heq : raw1097step0 = (fun i j => raw1097 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1097 permutation36 permutation15
    _ = injectiveMoment H node1475 := by rfl

def raw1098 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw1098step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, 0, -2]]

theorem canonical1098 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1098 = injectiveMoment H node395 := by
  calc
    injectiveMoment H raw1098 = injectiveMoment H raw1098step0 := by
      have heq : raw1098step0 = (fun i j => raw1098 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1098 permutation10 permutation15
    _ = injectiveMoment H node395 := by rfl

def raw1099 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw1099step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 0, 2], ![0, 2, -1, -1], ![4, -2, 0, -2]]

def raw1099step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, 0, 0, -2], ![0, -2, 1, 1], ![-4, 2, 0, 2]]

def raw1099step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -2, 1, 0]]

theorem canonical1099 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1099 = injectiveMoment H node1257 := by
  calc
    injectiveMoment H raw1099 = injectiveMoment H raw1099step0 := by
      have heq : raw1099step0 = raw1099.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1099).symm
    injectiveMoment H raw1099step0 = injectiveMoment H raw1099step1 := by
      have heq : raw1099step1 = -raw1099step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1099step0).symm
    injectiveMoment H raw1099step1 = injectiveMoment H raw1099step2 := by
      have heq : raw1099step2 = (fun i j => raw1099step1 (permutation10 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1099step1 permutation10 permutation24
    _ = injectiveMoment H node1257 := by rfl

def raw1100 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw1100step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 0, 2], ![0, 2, 0, -2], ![4, -2, -1, -1]]

def raw1100step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 1, -2]]

theorem canonical1100 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1100 = injectiveMoment H node773 := by
  calc
    injectiveMoment H raw1100 = injectiveMoment H raw1100step0 := by
      have heq : raw1100step0 = raw1100.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1100).symm
    injectiveMoment H raw1100step0 = injectiveMoment H raw1100step1 := by
      have heq : raw1100step1 = (fun i j => raw1100step0 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1100step0 permutation30 permutation24
    _ = injectiveMoment H node773 := by rfl

def raw1101 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical1101 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1101 = injectiveMoment H node397 := by
  rfl

def raw1102 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -1, -1], ![1, 1, -1, -1]]

theorem canonical1102 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1102 = injectiveMoment H node398 := by
  rfl

def raw1103 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, 0, -2], ![1, 1, -2, 0]]

def raw1103step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical1103 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1103 = injectiveMoment H node397 := by
  calc
    injectiveMoment H raw1103 = injectiveMoment H raw1103step0 := by
      have heq : raw1103step0 = (fun i j => raw1103 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1103 permutation10 permutation9
    _ = injectiveMoment H node397 := by rfl

def raw1104 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 2, -4]]

def raw1104step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![0, -2, 0, 2], ![4, 1, -1, -4]]

def raw1104step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![0, 2, 0, -2], ![-4, -1, 1, 4]]

def raw1104step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, -2, 0], ![1, -1, 4, -4]]

theorem canonical1104 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1104 = injectiveMoment H node1034 := by
  calc
    injectiveMoment H raw1104 = injectiveMoment H raw1104step0 := by
      have heq : raw1104step0 = raw1104.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1104).symm
    injectiveMoment H raw1104step0 = injectiveMoment H raw1104step1 := by
      have heq : raw1104step1 = -raw1104step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1104step0).symm
    injectiveMoment H raw1104step1 = injectiveMoment H raw1104step2 := by
      have heq : raw1104step2 = (fun i j => raw1104step1 (permutation15 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1104step1 permutation15 permutation24
    _ = injectiveMoment H node1034 := by rfl

def raw1105 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical1105 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1105 = injectiveMoment H node1481 := by
  rfl

def raw1106 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw1106step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical1106 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1106 = injectiveMoment H node1481 := by
  calc
    injectiveMoment H raw1106 = injectiveMoment H raw1106step0 := by
      have heq : raw1106step0 = (fun i j => raw1106 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1106 permutation34 permutation9
    _ = injectiveMoment H node1481 := by rfl

def raw1107 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 1, -3]]

theorem canonical1107 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1107 = injectiveMoment H node400 := by
  rfl

def raw1108 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical1108 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1108 = injectiveMoment H node1482 := by
  rfl

def raw1109 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, 0, 0, -2]]

theorem canonical1109 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1109 = injectiveMoment H node401 := by
  rfl

def raw1110 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 2, -4]]

def raw1110step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![0, -2, 0, 2], ![4, 1, -1, -4]]

def raw1110step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, 0, -1], ![0, 2, 0, -2], ![-4, -1, 1, 4]]

def raw1110step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, -1, 4, -4]]

theorem canonical1110 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1110 = injectiveMoment H node1238 := by
  calc
    injectiveMoment H raw1110 = injectiveMoment H raw1110step0 := by
      have heq : raw1110step0 = raw1110.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1110).symm
    injectiveMoment H raw1110step0 = injectiveMoment H raw1110step1 := by
      have heq : raw1110step1 = -raw1110step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1110step0).symm
    injectiveMoment H raw1110step1 = injectiveMoment H raw1110step2 := by
      have heq : raw1110step2 = (fun i j => raw1110step1 (permutation9 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1110step1 permutation9 permutation24
    _ = injectiveMoment H node1238 := by rfl

def raw1111 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 1, -3]]

theorem canonical1111 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1111 = injectiveMoment H node402 := by
  rfl

def raw1112 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 2, -3], ![1, 1, 0, -2]]

theorem canonical1112 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1112 = injectiveMoment H node403 := by
  rfl

def raw1113 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 1, 1, -3], ![1, 0, 1, -2]]

def raw1113step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 1, -3]]

theorem canonical1113 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1113 = injectiveMoment H node402 := by
  calc
    injectiveMoment H raw1113 = injectiveMoment H raw1113step0 := by
      have heq : raw1113step0 = (fun i j => raw1113 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1113 permutation10 permutation9
    _ = injectiveMoment H node402 := by rfl

def raw1114 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 1, 2, -4], ![1, 0, 0, -1]]

def raw1114step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![0, -2, 2, 0], ![4, 1, -4, -1]]

def raw1114step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, -1, 0], ![0, 2, -2, 0], ![-4, -1, 4, 1]]

def raw1114step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, -1, 4, -4]]

theorem canonical1114 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1114 = injectiveMoment H node1238 := by
  calc
    injectiveMoment H raw1114 = injectiveMoment H raw1114step0 := by
      have heq : raw1114step0 = raw1114.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1114).symm
    injectiveMoment H raw1114step0 = injectiveMoment H raw1114step1 := by
      have heq : raw1114step1 = -raw1114step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1114step0).symm
    injectiveMoment H raw1114step1 = injectiveMoment H raw1114step2 := by
      have heq : raw1114step2 = (fun i j => raw1114step1 (permutation9 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1114step1 permutation9 permutation30
    _ = injectiveMoment H node1238 := by rfl

def raw1115 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

theorem canonical1115 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1115 = injectiveMoment H node1483 := by
  rfl

def raw1116 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 2, -3]]

theorem canonical1116 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1116 = injectiveMoment H node1484 := by
  rfl

def raw1117 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 0, 1, -2]]

theorem canonical1117 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1117 = injectiveMoment H node1485 := by
  rfl

def raw1118 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw1118step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![0, -1, -1, 2], ![4, 0, 0, -4]]

def raw1118step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 4, -4], ![1, 1, -2, 0]]

theorem canonical1118 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1118 = injectiveMoment H node1029 := by
  calc
    injectiveMoment H raw1118 = injectiveMoment H raw1118step0 := by
      have heq : raw1118step0 = raw1118.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1118).symm
    injectiveMoment H raw1118step0 = injectiveMoment H raw1118step1 := by
      have heq : raw1118step1 = (fun i j => raw1118step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1118step0 permutation22 permutation17
    _ = injectiveMoment H node1029 := by rfl

def raw1119 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

theorem canonical1119 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1119 = injectiveMoment H node1486 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
