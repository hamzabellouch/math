import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1120 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1120step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, 1, 0], ![0, -1, 0, 1], ![-1, 0, 0, 1], ![-1, 0, -1, 2]]

def raw1120step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical1120 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1120 = injectiveMoment H node2578 := by
  calc
    injectiveMoment H raw1120 = injectiveMoment H raw1120step0 := by
      have heq : raw1120step0 = -raw1120 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1120).symm
    injectiveMoment H raw1120step0 = injectiveMoment H raw1120step1 := by
      have heq : raw1120step1 = (fun i j => raw1120step0 (permutation149 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1120step0 permutation149 permutation21
    _ = injectiveMoment H node2578 := by rfl

def raw1121 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def raw1121step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![0, -1, 0, 1], ![4, 0, -1, -3]]

def raw1121step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![0, 1, 0, -1], ![-4, 0, 1, 3]]

def raw1121step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem canonical1121 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1121 = injectiveMoment H node1031 := by
  calc
    injectiveMoment H raw1121 = injectiveMoment H raw1121step0 := by
      have heq : raw1121step0 = raw1121.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1121).symm
    injectiveMoment H raw1121step0 = injectiveMoment H raw1121step1 := by
      have heq : raw1121step1 = -raw1121step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1121step0).symm
    injectiveMoment H raw1121step1 = injectiveMoment H raw1121step2 := by
      have heq : raw1121step2 = (fun i j => raw1121step1 (permutation15 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1121step1 permutation15 permutation24
    _ = injectiveMoment H node1031 := by rfl

def raw1122 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical1122 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1122 = injectiveMoment H node1487 := by
  rfl

def raw1123 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1123step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, 1, 0], ![0, -1, -1, 2], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw1123step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

theorem canonical1123 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1123 = injectiveMoment H node2596 := by
  calc
    injectiveMoment H raw1123 = injectiveMoment H raw1123step0 := by
      have heq : raw1123step0 = -raw1123 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1123).symm
    injectiveMoment H raw1123step0 = injectiveMoment H raw1123step1 := by
      have heq : raw1123step1 = (fun i j => raw1123step0 (permutation96 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1123step0 permutation96 permutation23
    _ = injectiveMoment H node2596 := by rfl

def raw1124 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

def raw1124step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, 1, 0], ![0, -1, -1, 2], ![-2, 0, 0, 2]]

def raw1124step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

theorem canonical1124 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1124 = injectiveMoment H node1037 := by
  calc
    injectiveMoment H raw1124 = injectiveMoment H raw1124step0 := by
      have heq : raw1124step0 = -raw1124 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1124).symm
    injectiveMoment H raw1124step0 = injectiveMoment H raw1124step1 := by
      have heq : raw1124step1 = (fun i j => raw1124step0 (permutation25 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1124step0 permutation25 permutation23
    _ = injectiveMoment H node1037 := by rfl

def raw1125 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1125step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

theorem canonical1125 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1125 = injectiveMoment H node1486 := by
  calc
    injectiveMoment H raw1125 = injectiveMoment H raw1125step0 := by
      have heq : raw1125step0 = (fun i j => raw1125 (permutation49 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1125 permutation49 permutation15
    _ = injectiveMoment H node1486 := by rfl

def raw1126 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, 0, -1, -1]]

def raw1126step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![0, -1, 2, -1], ![4, 0, -3, -1]]

def raw1126step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical1126 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1126 = injectiveMoment H node1155 := by
  calc
    injectiveMoment H raw1126 = injectiveMoment H raw1126step0 := by
      have heq : raw1126step0 = raw1126.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1126).symm
    injectiveMoment H raw1126step0 = injectiveMoment H raw1126step1 := by
      have heq : raw1126step1 = (fun i j => raw1126step0 (permutation25 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1126step0 permutation25 permutation20
    _ = injectiveMoment H node1155 := by rfl

def raw1127 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1127step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

theorem canonical1127 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1127 = injectiveMoment H node1483 := by
  calc
    injectiveMoment H raw1127 = injectiveMoment H raw1127step0 := by
      have heq : raw1127step0 = (fun i j => raw1127 (permutation49 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1127 permutation49 permutation15
    _ = injectiveMoment H node1483 := by rfl

def raw1128 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw1128step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![0, -1, -1, 2], ![4, 0, 0, -4]]

def raw1128step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, 0, -2, 1]]

theorem canonical1128 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1128 = injectiveMoment H node1070 := by
  calc
    injectiveMoment H raw1128 = injectiveMoment H raw1128step0 := by
      have heq : raw1128step0 = raw1128.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1128).symm
    injectiveMoment H raw1128step0 = injectiveMoment H raw1128step1 := by
      have heq : raw1128step1 = (fun i j => raw1128step0 (permutation25 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1128step0 permutation25 permutation17
    _ = injectiveMoment H node1070 := by rfl

def raw1129 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw1129step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![0, -1, 0, 1], ![4, 0, -1, -3]]

def raw1129step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1129 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1129 = injectiveMoment H node1168 := by
  calc
    injectiveMoment H raw1129 = injectiveMoment H raw1129step0 := by
      have heq : raw1129step0 = raw1129.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1129).symm
    injectiveMoment H raw1129step0 = injectiveMoment H raw1129step1 := by
      have heq : raw1129step1 = (fun i j => raw1129step0 (permutation32 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1129step0 permutation32 permutation24
    _ = injectiveMoment H node1168 := by rfl

def raw1130 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

def raw1130step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, 1, 0], ![-1, 0, -1, 2], ![-1, -1, 0, 2]]

def raw1130step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical1130 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1130 = injectiveMoment H node998 := by
  calc
    injectiveMoment H raw1130 = injectiveMoment H raw1130step0 := by
      have heq : raw1130step0 = -raw1130 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1130).symm
    injectiveMoment H raw1130step0 = injectiveMoment H raw1130step1 := by
      have heq : raw1130step1 = (fun i j => raw1130step0 (permutation25 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1130step0 permutation25 permutation21
    _ = injectiveMoment H node998 := by rfl

def raw1131 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 0, 2, -3], ![1, 1, -1, -1]]

def raw1131step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![0, -1, 2, -1], ![4, 0, -3, -1]]

def raw1131step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, 0, -1], ![0, 1, -2, 1], ![-4, 0, 3, 1]]

def raw1131step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem canonical1131 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1131 = injectiveMoment H node996 := by
  calc
    injectiveMoment H raw1131 = injectiveMoment H raw1131step0 := by
      have heq : raw1131step0 = raw1131.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1131).symm
    injectiveMoment H raw1131step0 = injectiveMoment H raw1131step1 := by
      have heq : raw1131step1 = -raw1131step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1131step0).symm
    injectiveMoment H raw1131step1 = injectiveMoment H raw1131step2 := by
      have heq : raw1131step2 = (fun i j => raw1131step1 (permutation16 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1131step1 permutation16 permutation20
    _ = injectiveMoment H node996 := by rfl

def raw1132 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 1, -2, 0], ![1, 0, 3, -4]]

def raw1132step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![0, -1, -2, 3], ![4, 0, 0, -4]]

def raw1132step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 4, -4], ![0, 1, -2, 1], ![1, 1, -2, 0]]

theorem canonical1132 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1132 = injectiveMoment H node813 := by
  calc
    injectiveMoment H raw1132 = injectiveMoment H raw1132step0 := by
      have heq : raw1132step0 = raw1132.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1132).symm
    injectiveMoment H raw1132step0 = injectiveMoment H raw1132step1 := by
      have heq : raw1132step1 = (fun i j => raw1132step0 (permutation25 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1132step0 permutation25 permutation17
    _ = injectiveMoment H node813 := by rfl

def raw1133 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 1, -1, -1], ![1, 0, 2, -3]]

def raw1133step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![0, -1, -1, 2], ![4, 0, -1, -3]]

def raw1133step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, -1, 0], ![0, 1, 1, -2], ![-4, 0, 1, 3]]

def raw1133step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem canonical1133 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1133 = injectiveMoment H node996 := by
  calc
    injectiveMoment H raw1133 = injectiveMoment H raw1133step0 := by
      have heq : raw1133step0 = raw1133.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1133).symm
    injectiveMoment H raw1133step0 = injectiveMoment H raw1133step1 := by
      have heq : raw1133step1 = -raw1133step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1133step0).symm
    injectiveMoment H raw1133step1 = injectiveMoment H raw1133step2 := by
      have heq : raw1133step2 = (fun i j => raw1133step1 (permutation16 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1133step1 permutation16 permutation18
    _ = injectiveMoment H node996 := by rfl

def raw1134 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![1, 1, 0, -2], ![1, 0, 1, -2]]

def raw1134step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, 1, 0], ![-1, -1, 0, 2], ![-1, 0, -1, 2]]

def raw1134step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical1134 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1134 = injectiveMoment H node998 := by
  calc
    injectiveMoment H raw1134 = injectiveMoment H raw1134step0 := by
      have heq : raw1134step0 = -raw1134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1134).symm
    injectiveMoment H raw1134step0 = injectiveMoment H raw1134step1 := by
      have heq : raw1134step1 = (fun i j => raw1134step0 (permutation31 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1134step0 permutation31 permutation21
    _ = injectiveMoment H node998 := by rfl

def raw1135 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1135step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, 0, 1], ![0, -1, 1, 0], ![-1, 0, 0, 1], ![-1, 0, -1, 2]]

def raw1135step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical1135 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1135 = injectiveMoment H node2578 := by
  calc
    injectiveMoment H raw1135 = injectiveMoment H raw1135step0 := by
      have heq : raw1135step0 = -raw1135 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1135).symm
    injectiveMoment H raw1135step0 = injectiveMoment H raw1135step1 := by
      have heq : raw1135step1 = (fun i j => raw1135step0 (permutation147 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1135step0 permutation147 permutation21
    _ = injectiveMoment H node2578 := by rfl

def raw1136 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw1136step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![0, 0, -1, 1], ![4, -1, 0, -3]]

def raw1136step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![0, 0, 1, -1], ![-4, 1, 0, 3]]

def raw1136step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem canonical1136 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1136 = injectiveMoment H node1031 := by
  calc
    injectiveMoment H raw1136 = injectiveMoment H raw1136step0 := by
      have heq : raw1136step0 = raw1136.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1136).symm
    injectiveMoment H raw1136step0 = injectiveMoment H raw1136step1 := by
      have heq : raw1136step1 = -raw1136step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1136step0).symm
    injectiveMoment H raw1136step1 = injectiveMoment H raw1136step2 := by
      have heq : raw1136step2 = (fun i j => raw1136step1 (permutation15 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1136step1 permutation15 permutation18
    _ = injectiveMoment H node1031 := by rfl

def raw1137 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1137step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, 0, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, -1, 2]]

def raw1137step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

theorem canonical1137 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1137 = injectiveMoment H node2596 := by
  calc
    injectiveMoment H raw1137 = injectiveMoment H raw1137step0 := by
      have heq : raw1137step0 = -raw1137 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1137).symm
    injectiveMoment H raw1137step0 = injectiveMoment H raw1137step1 := by
      have heq : raw1137step1 = (fun i j => raw1137step0 (permutation135 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1137step0 permutation135 permutation21
    _ = injectiveMoment H node2596 := by rfl

def raw1138 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1138step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, 0, 1], ![0, -1, -1, 2], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw1138step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical1138 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1138 = injectiveMoment H node2578 := by
  calc
    injectiveMoment H raw1138 = injectiveMoment H raw1138step0 := by
      have heq : raw1138step0 = -raw1138 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1138).symm
    injectiveMoment H raw1138step0 = injectiveMoment H raw1138step1 := by
      have heq : raw1138step1 = (fun i j => raw1138step0 (permutation90 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1138step0 permutation90 permutation23
    _ = injectiveMoment H node2578 := by rfl

def raw1139 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

def raw1139step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![0, 0, 1, -1], ![4, -1, -2, -1]]

def raw1139step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical1139 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1139 = injectiveMoment H node771 := by
  calc
    injectiveMoment H raw1139 = injectiveMoment H raw1139step0 := by
      have heq : raw1139step0 = raw1139.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1139).symm
    injectiveMoment H raw1139step0 = injectiveMoment H raw1139step1 := by
      have heq : raw1139step1 = (fun i j => raw1139step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1139step0 permutation28 permutation18
    _ = injectiveMoment H node771 := by rfl

def raw1140 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1140step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 2, -3]]

theorem canonical1140 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1140 = injectiveMoment H node1484 := by
  calc
    injectiveMoment H raw1140 = injectiveMoment H raw1140step0 := by
      have heq : raw1140step0 = (fun i j => raw1140 (permutation49 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1140 permutation49 permutation15
    _ = injectiveMoment H node1484 := by rfl

def raw1141 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![0, 1, 2, -3], ![2, 0, -2, 0]]

def raw1141step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![0, 0, 2, -2], ![4, -1, -3, 0]]

def raw1141step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical1141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1141 = injectiveMoment H node1164 := by
  calc
    injectiveMoment H raw1141 = injectiveMoment H raw1141step0 := by
      have heq : raw1141step0 = raw1141.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1141).symm
    injectiveMoment H raw1141step0 = injectiveMoment H raw1141step1 := by
      have heq : raw1141step1 = (fun i j => raw1141step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1141step0 permutation31 permutation20
    _ = injectiveMoment H node1164 := by rfl

def raw1142 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 1, 1, -3]]

def raw1142step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![0, 0, -1, 1], ![4, -1, 0, -3]]

def raw1142step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1142 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1142 = injectiveMoment H node1168 := by
  calc
    injectiveMoment H raw1142 = injectiveMoment H raw1142step0 := by
      have heq : raw1142step0 = raw1142.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1142).symm
    injectiveMoment H raw1142step0 = injectiveMoment H raw1142step1 := by
      have heq : raw1142step1 = (fun i j => raw1142step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1142step0 permutation31 permutation18
    _ = injectiveMoment H node1168 := by rfl

def raw1143 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw1143step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![0, 0, 1, -1], ![4, -1, -2, -1]]

def raw1143step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1143 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1143 = injectiveMoment H node786 := by
  calc
    injectiveMoment H raw1143 = injectiveMoment H raw1143step0 := by
      have heq : raw1143step0 = raw1143.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1143).symm
    injectiveMoment H raw1143step0 = injectiveMoment H raw1143step1 := by
      have heq : raw1143step1 = (fun i j => raw1143step0 (permutation31 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1143step0 permutation31 permutation18
    _ = injectiveMoment H node786 := by rfl

def raw1144 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![1, 0, 2, -3], ![1, 1, -2, 0]]

def raw1144step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![0, 0, 2, -2], ![4, -1, -3, 0]]

def raw1144step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, 0, -1], ![0, 0, -2, 2], ![-4, 1, 3, 0]]

def raw1144step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 3, -4]]

theorem canonical1144 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1144 = injectiveMoment H node997 := by
  calc
    injectiveMoment H raw1144 = injectiveMoment H raw1144step0 := by
      have heq : raw1144step0 = raw1144.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1144).symm
    injectiveMoment H raw1144step0 = injectiveMoment H raw1144step1 := by
      have heq : raw1144step1 = -raw1144step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1144step0).symm
    injectiveMoment H raw1144step1 = injectiveMoment H raw1144step2 := by
      have heq : raw1144step2 = (fun i j => raw1144step1 (permutation15 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1144step1 permutation15 permutation20
    _ = injectiveMoment H node997 := by rfl

def raw1145 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 0, -1], ![1, 1, -2, 0], ![1, 0, 2, -3]]

def raw1145step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![0, 0, -2, 2], ![4, -1, 0, -3]]

def raw1145step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, -1, 0], ![0, 0, 2, -2], ![-4, 1, 0, 3]]

def raw1145step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 3, -4]]

theorem canonical1145 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1145 = injectiveMoment H node997 := by
  calc
    injectiveMoment H raw1145 = injectiveMoment H raw1145step0 := by
      have heq : raw1145step0 = raw1145.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1145).symm
    injectiveMoment H raw1145step0 = injectiveMoment H raw1145step1 := by
      have heq : raw1145step1 = -raw1145step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1145step0).symm
    injectiveMoment H raw1145step1 = injectiveMoment H raw1145step2 := by
      have heq : raw1145step2 = (fun i j => raw1145step1 (permutation15 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1145step1 permutation15 permutation18
    _ = injectiveMoment H node997 := by rfl

def raw1146 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1146step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, -1, 2], ![0, -1, 1, 0], ![-1, 0, 0, 1], ![-1, 0, 0, 1]]

def raw1146step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, -1, 0, 0]]

theorem canonical1146 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1146 = injectiveMoment H node2596 := by
  calc
    injectiveMoment H raw1146 = injectiveMoment H raw1146step0 := by
      have heq : raw1146step0 = -raw1146 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1146).symm
    injectiveMoment H raw1146step0 = injectiveMoment H raw1146step1 := by
      have heq : raw1146step1 = (fun i j => raw1146step0 (permutation72 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1146step0 permutation72 permutation23
    _ = injectiveMoment H node2596 := by rfl

def raw1147 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![0, 1, -1, 0], ![2, 0, 0, -2]]

def raw1147step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, -1, 2], ![0, -1, 1, 0], ![-2, 0, 0, 2]]

def raw1147step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

theorem canonical1147 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1147 = injectiveMoment H node1037 := by
  calc
    injectiveMoment H raw1147 = injectiveMoment H raw1147step0 := by
      have heq : raw1147step0 = -raw1147 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1147).symm
    injectiveMoment H raw1147step0 = injectiveMoment H raw1147step1 := by
      have heq : raw1147step1 = (fun i j => raw1147step0 (permutation19 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1147step0 permutation19 permutation23
    _ = injectiveMoment H node1037 := by rfl

def raw1148 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1148step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, -1, 2], ![0, -1, 0, 1], ![-1, 0, 1, 0], ![-1, 0, 0, 1]]

def raw1148step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical1148 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1148 = injectiveMoment H node2578 := by
  calc
    injectiveMoment H raw1148 = injectiveMoment H raw1148step0 := by
      have heq : raw1148step0 = -raw1148 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1148).symm
    injectiveMoment H raw1148step0 = injectiveMoment H raw1148step1 := by
      have heq : raw1148step1 = (fun i j => raw1148step0 (permutation66 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1148step0 permutation66 permutation23
    _ = injectiveMoment H node2578 := by rfl

def raw1149 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw1149step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![0, 1, 0, -1], ![4, -2, -1, -1]]

def raw1149step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical1149 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1149 = injectiveMoment H node771 := by
  calc
    injectiveMoment H raw1149 = injectiveMoment H raw1149step0 := by
      have heq : raw1149step0 = raw1149.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1149).symm
    injectiveMoment H raw1149step0 = injectiveMoment H raw1149step1 := by
      have heq : raw1149step1 = (fun i j => raw1149step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1149step0 permutation28 permutation24
    _ = injectiveMoment H node771 := by rfl

def raw1150 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![0, 1, 1, -2], ![2, 0, -2, 0]]

def raw1150step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![0, 1, 1, -2], ![4, -2, -2, 0]]

def raw1150step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical1150 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1150 = injectiveMoment H node397 := by
  calc
    injectiveMoment H raw1150 = injectiveMoment H raw1150step0 := by
      have heq : raw1150step0 = raw1150.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1150).symm
    injectiveMoment H raw1150step0 = injectiveMoment H raw1150step1 := by
      have heq : raw1150step1 = (fun i j => raw1150step0 (permutation28 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1150step0 permutation28 permutation18
    _ = injectiveMoment H node397 := by rfl

def raw1151 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 1, 0, -2]]

def raw1151step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -1, -1, 2], ![-1, 0, 1, 0], ![-1, -1, 0, 2]]

def raw1151step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical1151 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1151 = injectiveMoment H node998 := by
  calc
    injectiveMoment H raw1151 = injectiveMoment H raw1151step0 := by
      have heq : raw1151step0 = -raw1151 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1151).symm
    injectiveMoment H raw1151step0 = injectiveMoment H raw1151step1 := by
      have heq : raw1151step1 = (fun i j => raw1151step0 (permutation19 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1151step0 permutation19 permutation23
    _ = injectiveMoment H node998 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
