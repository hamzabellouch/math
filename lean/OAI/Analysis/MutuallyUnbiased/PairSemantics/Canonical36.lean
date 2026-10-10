import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1152 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 1, -1, -1]]

def raw1152step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![0, 1, 0, -1], ![4, -2, -1, -1]]

def raw1152step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

theorem canonical1152 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1152 = injectiveMoment H node786 := by
  calc
    injectiveMoment H raw1152 = injectiveMoment H raw1152step0 := by
      have heq : raw1152step0 = raw1152.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1152).symm
    injectiveMoment H raw1152step0 = injectiveMoment H raw1152step1 := by
      have heq : raw1152step1 = (fun i j => raw1152step0 (permutation32 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1152step0 permutation32 permutation24
    _ = injectiveMoment H node786 := by rfl

def raw1153 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -2, 0]]

theorem canonical1153 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1153 = injectiveMoment H node404 := by
  rfl

def raw1154 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![1, 1, -2, 0], ![1, 0, 1, -2]]

def raw1154step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -2, 0]]

theorem canonical1154 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1154 = injectiveMoment H node404 := by
  calc
    injectiveMoment H raw1154 = injectiveMoment H raw1154step0 := by
      have heq : raw1154step0 = (fun i j => raw1154 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1154 permutation10 permutation9
    _ = injectiveMoment H node404 := by rfl

def raw1155 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 2, -3], ![0, 1, -2, 1], ![2, 0, 0, -2]]

def raw1155step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, 0, 0, -2]]

theorem canonical1155 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1155 = injectiveMoment H node401 := by
  calc
    injectiveMoment H raw1155 = injectiveMoment H raw1155step0 := by
      have heq : raw1155step0 = (fun i j => raw1155 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1155 permutation11 permutation9
    _ = injectiveMoment H node401 := by rfl

def raw1156 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 2, -3], ![0, 1, 0, -1], ![2, 0, -2, 0]]

def raw1156step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![0, 2, 0, -2], ![4, -3, -1, 0]]

def raw1156step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical1156 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1156 = injectiveMoment H node1164 := by
  calc
    injectiveMoment H raw1156 = injectiveMoment H raw1156step0 := by
      have heq : raw1156step0 = raw1156.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1156).symm
    injectiveMoment H raw1156step0 = injectiveMoment H raw1156step1 := by
      have heq : raw1156step1 = (fun i j => raw1156step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1156step0 permutation31 permutation26
    _ = injectiveMoment H node1164 := by rfl

def raw1157 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 2, -3], ![1, 0, -1, 0], ![1, 1, -1, -1]]

def raw1157step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![0, 2, -1, -1], ![4, -3, 0, -1]]

def raw1157step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, 0, -1], ![0, -2, 1, 1], ![-4, 3, 0, 1]]

def raw1157step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem canonical1157 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1157 = injectiveMoment H node996 := by
  calc
    injectiveMoment H raw1157 = injectiveMoment H raw1157step0 := by
      have heq : raw1157step0 = raw1157.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1157).symm
    injectiveMoment H raw1157step0 = injectiveMoment H raw1157step1 := by
      have heq : raw1157step1 = -raw1157step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1157step0).symm
    injectiveMoment H raw1157step1 = injectiveMoment H raw1157step2 := by
      have heq : raw1157step2 = (fun i j => raw1157step1 (permutation10 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1157step1 permutation10 permutation26
    _ = injectiveMoment H node996 := by rfl

def raw1158 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 2, -3], ![1, 0, 0, -1], ![1, 1, -2, 0]]

def raw1158step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![0, 2, 0, -2], ![4, -3, -1, 0]]

def raw1158step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, 0, -1], ![0, -2, 0, 2], ![-4, 3, 1, 0]]

def raw1158step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 3, -4]]

theorem canonical1158 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1158 = injectiveMoment H node997 := by
  calc
    injectiveMoment H raw1158 = injectiveMoment H raw1158step0 := by
      have heq : raw1158step0 = raw1158.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1158).symm
    injectiveMoment H raw1158step0 = injectiveMoment H raw1158step1 := by
      have heq : raw1158step1 = -raw1158step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1158step0).symm
    injectiveMoment H raw1158step1 = injectiveMoment H raw1158step2 := by
      have heq : raw1158step2 = (fun i j => raw1158step1 (permutation9 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1158step1 permutation9 permutation26
    _ = injectiveMoment H node997 := by rfl

def raw1159 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 2, -2, 0], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw1159step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![0, -2, -1, 3], ![4, 0, 0, -4]]

def raw1159step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 4, -4], ![0, 2, -2, 0], ![1, 0, -2, 1]]

theorem canonical1159 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1159 = injectiveMoment H node814 := by
  calc
    injectiveMoment H raw1159 = injectiveMoment H raw1159step0 := by
      have heq : raw1159step0 = raw1159.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1159).symm
    injectiveMoment H raw1159step0 = injectiveMoment H raw1159step1 := by
      have heq : raw1159step1 = (fun i j => raw1159step0 (permutation26 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1159step0 permutation26 permutation23
    _ = injectiveMoment H node814 := by rfl

def raw1160 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 2, -3]]

def raw1160step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![0, -2, 0, 2], ![4, 0, -1, -3]]

def raw1160step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical1160 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1160 = injectiveMoment H node1164 := by
  calc
    injectiveMoment H raw1160 = injectiveMoment H raw1160step0 := by
      have heq : raw1160step0 = raw1160.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1160).symm
    injectiveMoment H raw1160step0 = injectiveMoment H raw1160step1 := by
      have heq : raw1160step1 = (fun i j => raw1160step0 (permutation32 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1160step0 permutation32 permutation24
    _ = injectiveMoment H node1164 := by rfl

def raw1161 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 2, -2, 0], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def raw1161step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![0, -2, 1, 1], ![4, 0, -2, -2]]

def raw1161step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 0, 2, -2], ![1, 1, -2, 0], ![1, 1, 0, -2]]

theorem canonical1161 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1161 = injectiveMoment H node397 := by
  calc
    injectiveMoment H raw1161 = injectiveMoment H raw1161step0 := by
      have heq : raw1161step0 = raw1161.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1161).symm
    injectiveMoment H raw1161step0 = injectiveMoment H raw1161step1 := by
      have heq : raw1161step1 = (fun i j => raw1161step0 (permutation30 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1161step0 permutation30 permutation26
    _ = injectiveMoment H node397 := by rfl

def raw1162 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw1162step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![0, -1, -1, 2], ![4, -1, 0, -3]]

def raw1162step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical1162 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1162 = injectiveMoment H node1155 := by
  calc
    injectiveMoment H raw1162 = injectiveMoment H raw1162step0 := by
      have heq : raw1162step0 = raw1162.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1162).symm
    injectiveMoment H raw1162step0 = injectiveMoment H raw1162step1 := by
      have heq : raw1162step1 = (fun i j => raw1162step0 (permutation26 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1162step0 permutation26 permutation24
    _ = injectiveMoment H node1155 := by rfl

def raw1163 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw1163step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![0, -1, 0, 1], ![4, -1, -1, -2]]

def raw1163step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 1, 0, -2]]

theorem canonical1163 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1163 = injectiveMoment H node771 := by
  calc
    injectiveMoment H raw1163 = injectiveMoment H raw1163step0 := by
      have heq : raw1163step0 = raw1163.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1163).symm
    injectiveMoment H raw1163step0 = injectiveMoment H raw1163step1 := by
      have heq : raw1163step1 = (fun i j => raw1163step0 (permutation30 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1163step0 permutation30 permutation26
    _ = injectiveMoment H node771 := by rfl

def raw1164 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw1164step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 2, 0, -4], ![0, -2, 0, 2], ![-1, 0, 1, 0], ![-1, 0, -1, 2]]

def raw1164step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

theorem canonical1164 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1164 = injectiveMoment H node1037 := by
  calc
    injectiveMoment H raw1164 = injectiveMoment H raw1164step0 := by
      have heq : raw1164step0 = -raw1164 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1164).symm
    injectiveMoment H raw1164step0 = injectiveMoment H raw1164step1 := by
      have heq : raw1164step1 = (fun i j => raw1164step0 (permutation29 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1164step0 permutation29 permutation21
    _ = injectiveMoment H node1037 := by rfl

def raw1165 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1165step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 2, 0, 0], ![0, 1, -1, 0], ![4, -3, 0, -1]]

def raw1165step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -2, 0, 0], ![0, -1, 1, 0], ![-4, 3, 0, 1]]

def raw1165step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, -1, 0], ![1, 0, 3, -4]]

theorem canonical1165 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1165 = injectiveMoment H node1031 := by
  calc
    injectiveMoment H raw1165 = injectiveMoment H raw1165step0 := by
      have heq : raw1165step0 = raw1165.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1165).symm
    injectiveMoment H raw1165step0 = injectiveMoment H raw1165step1 := by
      have heq : raw1165step1 = -raw1165step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1165step0).symm
    injectiveMoment H raw1165step1 = injectiveMoment H raw1165step2 := by
      have heq : raw1165step2 = (fun i j => raw1165step1 (permutation9 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1165step1 permutation9 permutation32
    _ = injectiveMoment H node1031 := by rfl

def raw1166 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![1, 0, 2, -3], ![0, 1, -2, 1], ![1, 1, 0, -2]]

def raw1166step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, -2, 1], ![1, 0, 2, -3], ![1, 1, 0, -2]]

theorem canonical1166 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1166 = injectiveMoment H node403 := by
  calc
    injectiveMoment H raw1166 = injectiveMoment H raw1166step0 := by
      have heq : raw1166step0 = (fun i j => raw1166 (permutation11 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1166 permutation11 permutation9
    _ = injectiveMoment H node403 := by rfl

def raw1167 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![1, 1, -2, 0], ![0, 1, 1, -2], ![1, 0, 1, -2]]

def raw1167step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![0, 1, 1, -2], ![1, 0, 1, -2], ![1, 1, -2, 0]]

theorem canonical1167 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1167 = injectiveMoment H node404 := by
  calc
    injectiveMoment H raw1167 = injectiveMoment H raw1167step0 := by
      have heq : raw1167step0 = (fun i j => raw1167 (permutation12 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1167 permutation12 permutation9
    _ = injectiveMoment H node404 := by rfl

def raw1168 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 0, 4], ![1, 1, -2, 0], ![0, 1, 2, -3], ![1, 0, 0, -1]]

def raw1168step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 1, 0, 1], ![-2, 1, 1, 0], ![0, -2, 2, 0], ![4, 0, -3, -1]]

def raw1168step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, -1, 0, -1], ![2, -1, -1, 0], ![0, 2, -2, 0], ![-4, 0, 3, 1]]

def raw1168step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, -1, 2], ![0, 2, -2, 0], ![1, 0, 3, -4]]

theorem canonical1168 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1168 = injectiveMoment H node997 := by
  calc
    injectiveMoment H raw1168 = injectiveMoment H raw1168step0 := by
      have heq : raw1168step0 = raw1168.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1168).symm
    injectiveMoment H raw1168step0 = injectiveMoment H raw1168step1 := by
      have heq : raw1168step1 = -raw1168step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1168step0).symm
    injectiveMoment H raw1168step1 = injectiveMoment H raw1168step2 := by
      have heq : raw1168step2 = (fun i j => raw1168step1 (permutation9 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1168step1 permutation9 permutation30
    _ = injectiveMoment H node997 := by rfl

def raw1169 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, 0, -3]]

theorem canonical1169 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1169 = injectiveMoment H node1488 := by
  rfl

def raw1170 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 1, -3]]

theorem canonical1170 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1170 = injectiveMoment H node1489 := by
  rfl

def raw1171 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem canonical1171 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1171 = injectiveMoment H node1490 := by
  rfl

def raw1172 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![2, 1, 1, -4]]

def raw1172step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![1, -2, 0, 1], ![3, 2, -1, -4]]

def raw1172step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, 0, -1, -1], ![-1, 2, 0, -1], ![-3, -2, 1, 4]]

def raw1172step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -2, 4, -3]]

theorem canonical1172 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1172 = injectiveMoment H node1254 := by
  calc
    injectiveMoment H raw1172 = injectiveMoment H raw1172step0 := by
      have heq : raw1172step0 = raw1172.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1172).symm
    injectiveMoment H raw1172step0 = injectiveMoment H raw1172step1 := by
      have heq : raw1172step1 = -raw1172step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1172step0).symm
    injectiveMoment H raw1172step1 = injectiveMoment H raw1172step2 := by
      have heq : raw1172step2 = (fun i j => raw1172step1 (permutation15 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1172step1 permutation15 permutation24
    _ = injectiveMoment H node1254 := by rfl

def raw1173 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1173step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem canonical1173 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1173 = injectiveMoment H node1490 := by
  calc
    injectiveMoment H raw1173 = injectiveMoment H raw1173step0 := by
      have heq : raw1173step0 = (fun i j => raw1173 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1173 permutation35 permutation9
    _ = injectiveMoment H node1490 := by rfl

def raw1174 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 1, 1, -2], ![2, 1, 0, -3]]

theorem canonical1174 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1174 = injectiveMoment H node405 := by
  rfl

def raw1175 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, 0, 1, -3]]

theorem canonical1175 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1175 = injectiveMoment H node406 := by
  rfl

def raw1176 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 2, 1, -3], ![2, 0, 0, -2]]

def raw1176step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -2, 2], ![0, 2, 0, -2], ![2, 0, 1, -3]]

theorem canonical1176 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1176 = injectiveMoment H node406 := by
  calc
    injectiveMoment H raw1176 = injectiveMoment H raw1176step0 := by
      have heq : raw1176step0 = (fun i j => raw1176 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1176 permutation10 permutation15
    _ = injectiveMoment H node406 := by rfl

def raw1177 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, 0, 0, -2]]

def raw1177step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 2, 0, -2], ![2, 0, 1, -3]]

theorem canonical1177 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1177 = injectiveMoment H node1491 := by
  calc
    injectiveMoment H raw1177 = injectiveMoment H raw1177step0 := by
      have heq : raw1177step0 = (fun i j => raw1177 (permutation34 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1177 permutation34 permutation15
    _ = injectiveMoment H node1491 := by rfl

def raw1178 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, 0, 0], ![0, 1, 0, -1], ![2, 1, 0, -3]]

def raw1178step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 0, 2], ![-2, 0, 0, 1, 1], ![1, -1, 0, 0, 0], ![3, 1, 0, -1, -3]]

def raw1178step1 : Matrix (Fin 4) (Fin 5) ℤ := ![![2, 0, 0, 0, -2], ![2, 0, 0, -1, -1], ![-1, 1, 0, 0, 0], ![-3, -1, 0, 1, 3]]

def raw1178step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, 0, -1, -1], ![-1, 1, 0, 0], ![-3, -1, 1, 3]]

def raw1178step3 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, -1, 3, -3]]

theorem canonical1178 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1178 = injectiveMoment H node1252 := by
  calc
    injectiveMoment H raw1178 = injectiveMoment H raw1178step0 := by
      have heq : raw1178step0 = raw1178.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1178).symm
    injectiveMoment H raw1178step0 = injectiveMoment H raw1178step1 := by
      have heq : raw1178step1 = -raw1178step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1178step0).symm
    injectiveMoment H raw1178step1 = injectiveMoment H raw1178step2 := by
      have hz : ∀ i, raw1178step1 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw1178step2 = (fun i j => raw1178step1 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw1178step1 permutation80 hz
    injectiveMoment H raw1178step2 = injectiveMoment H raw1178step3 := by
      have heq : raw1178step3 = (fun i j => raw1178step2 (permutation15 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1178step2 permutation15 permutation24
    _ = injectiveMoment H node1252 := by rfl

def raw1179 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

theorem canonical1179 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1179 = injectiveMoment H node1492 := by
  rfl

def raw1180 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

theorem canonical1180 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1180 = injectiveMoment H node1493 := by
  rfl

def raw1181 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 2, -4]]

theorem canonical1181 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1181 = injectiveMoment H node1494 := by
  rfl

def raw1182 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem canonical1182 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1182 = injectiveMoment H node1496 := by
  rfl

def raw1183 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![1, 0, -1, 0], ![1, 1, 2, -4]]

theorem canonical1183 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1183 = injectiveMoment H node1497 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
