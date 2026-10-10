import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes44

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1216 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -2, -1]]

def raw1216step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![1, 1, 0, -2], ![3, -1, -1, -1]]

def raw1216step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical1216 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1216 = injectiveMoment H node973 := by
  calc
    injectiveMoment H raw1216 = injectiveMoment H raw1216step0 := by
      have heq : raw1216step0 = raw1216.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1216).symm
    injectiveMoment H raw1216step0 = injectiveMoment H raw1216step1 := by
      have heq : raw1216step1 = (fun i j => raw1216step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1216step0 permutation28 permutation24
    _ = injectiveMoment H node973 := by rfl

def raw1217 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1217step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -2, 0]]

theorem canonical1217 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1217 = injectiveMoment H node1507 := by
  calc
    injectiveMoment H raw1217 = injectiveMoment H raw1217step0 := by
      have heq : raw1217step0 = (fun i j => raw1217 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1217 permutation36 permutation15
    _ = injectiveMoment H node1507 := by rfl

def raw1218 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 2, -2, 0], ![2, 0, 0, -2]]

def raw1218step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![1, 1, -2, 0], ![3, -1, 0, -2]]

def raw1218step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical1218 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1218 = injectiveMoment H node808 := by
  calc
    injectiveMoment H raw1218 = injectiveMoment H raw1218step0 := by
      have heq : raw1218step0 = raw1218.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1218).symm
    injectiveMoment H raw1218step0 = injectiveMoment H raw1218step1 := by
      have heq : raw1218step1 = (fun i j => raw1218step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1218step0 permutation29 permutation20
    _ = injectiveMoment H node808 := by rfl

def raw1219 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1219step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical1219 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1219 = injectiveMoment H node1504 := by
  calc
    injectiveMoment H raw1219 = injectiveMoment H raw1219step0 := by
      have heq : raw1219step0 = (fun i j => raw1219 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1219 permutation36 permutation15
    _ = injectiveMoment H node1504 := by rfl

def raw1220 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 2, -1, -1], ![2, 0, -1, -1]]

def raw1220step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![1, 1, -1, -1], ![3, -1, -1, -1]]

def raw1220step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -1, 1]]

theorem canonical1220 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1220 = injectiveMoment H node976 := by
  calc
    injectiveMoment H raw1220 = injectiveMoment H raw1220step0 := by
      have heq : raw1220step0 = raw1220.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1220).symm
    injectiveMoment H raw1220step0 = injectiveMoment H raw1220step1 := by
      have heq : raw1220step1 = (fun i j => raw1220step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1220step0 permutation27 permutation18
    _ = injectiveMoment H node976 := by rfl

def raw1221 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw1221step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 0, -2]]

theorem canonical1221 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1221 = injectiveMoment H node1503 := by
  calc
    injectiveMoment H raw1221 = injectiveMoment H raw1221step0 := by
      have heq : raw1221step0 = (fun i j => raw1221 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1221 permutation36 permutation15
    _ = injectiveMoment H node1503 := by rfl

def raw1222 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![2, 0, -2, 0]]

def raw1222step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![1, 1, 0, -2], ![3, -1, -2, 0]]

def raw1222step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical1222 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1222 = injectiveMoment H node808 := by
  calc
    injectiveMoment H raw1222 = injectiveMoment H raw1222step0 := by
      have heq : raw1222step0 = raw1222.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1222).symm
    injectiveMoment H raw1222step0 = injectiveMoment H raw1222step1 := by
      have heq : raw1222step1 = (fun i j => raw1222step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1222step0 permutation27 permutation18
    _ = injectiveMoment H node808 := by rfl

def raw1223 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, -1, -2]]

def raw1223step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 0, 2], ![1, 1, -1, -1], ![3, -1, 0, -2]]

def raw1223step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, -1, 1]]

theorem canonical1223 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1223 = injectiveMoment H node1222 := by
  calc
    injectiveMoment H raw1223 = injectiveMoment H raw1223step0 := by
      have heq : raw1223step0 = raw1223.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1223).symm
    injectiveMoment H raw1223step0 = injectiveMoment H raw1223step1 := by
      have heq : raw1223step1 = (fun i j => raw1223step0 (permutation29 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1223step0 permutation29 permutation18
    _ = injectiveMoment H node1222 := by rfl

def raw1224 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -2, -1]]

def raw1224step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 0, 2], ![1, 1, 0, -2], ![3, -1, -1, -1]]

def raw1224step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 0, 2, -2], ![0, 1, -2, 1], ![1, 0, 1, -2]]

theorem canonical1224 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1224 = injectiveMoment H node973 := by
  calc
    injectiveMoment H raw1224 = injectiveMoment H raw1224step0 := by
      have heq : raw1224step0 = raw1224.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1224).symm
    injectiveMoment H raw1224step0 = injectiveMoment H raw1224step1 := by
      have heq : raw1224step1 = (fun i j => raw1224step0 (permutation30 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1224step0 permutation30 permutation24
    _ = injectiveMoment H node973 := by rfl

def raw1225 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 1, -1], ![1, 1, -2, 0], ![1, 1, 0, -2]]

def raw1225step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 0, 1, 1], ![1, 1, -2, 0], ![3, -1, 0, -2]]

def raw1225step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -2, 1]]

theorem canonical1225 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1225 = injectiveMoment H node820 := by
  calc
    injectiveMoment H raw1225 = injectiveMoment H raw1225step0 := by
      have heq : raw1225step0 = raw1225.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1225).symm
    injectiveMoment H raw1225step0 = injectiveMoment H raw1225step1 := by
      have heq : raw1225step1 = (fun i j => raw1225step0 (permutation27 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1225step0 permutation27 permutation20
    _ = injectiveMoment H node820 := by rfl

def raw1226 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 1, -2, -1]]

def raw1226step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![1, 2, -1, -2], ![3, -2, 0, -1]]

def raw1226step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, 0, -1, -1], ![-1, -2, 1, 2], ![-3, 2, 0, 1]]

def raw1226step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 1, -3], ![1, -2, 2, -1]]

theorem canonical1226 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1226 = injectiveMoment H node1256 := by
  calc
    injectiveMoment H raw1226 = injectiveMoment H raw1226step0 := by
      have heq : raw1226step0 = raw1226.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1226).symm
    injectiveMoment H raw1226step0 = injectiveMoment H raw1226step1 := by
      have heq : raw1226step1 = -raw1226step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1226step0).symm
    injectiveMoment H raw1226step1 = injectiveMoment H raw1226step2 := by
      have heq : raw1226step2 = (fun i j => raw1226step1 (permutation16 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1226step1 permutation16 permutation24
    _ = injectiveMoment H node1256 := by rfl

def raw1227 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![2, 0, -1, -1]]

def raw1227step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 2, 0], ![1, 2, -2, -1], ![3, -2, 0, -1]]

def raw1227step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, -1, -2, 1]]

theorem canonical1227 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1227 = injectiveMoment H node482 := by
  calc
    injectiveMoment H raw1227 = injectiveMoment H raw1227step0 := by
      have heq : raw1227step0 = raw1227.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1227).symm
    injectiveMoment H raw1227step0 = injectiveMoment H raw1227step1 := by
      have heq : raw1227step1 = (fun i j => raw1227step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1227step0 permutation29 permutation20
    _ = injectiveMoment H node482 := by rfl

def raw1228 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, 0, 2, -4]]

def raw1228step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, -2, -1, 2], ![3, 1, 0, -4]]

def raw1228step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem canonical1228 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1228 = injectiveMoment H node830 := by
  calc
    injectiveMoment H raw1228 = injectiveMoment H raw1228step0 := by
      have heq : raw1228step0 = raw1228.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1228).symm
    injectiveMoment H raw1228step0 = injectiveMoment H raw1228step1 := by
      have heq : raw1228step1 = (fun i j => raw1228step0 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1228step0 permutation22 permutation23
    _ = injectiveMoment H node830 := by rfl

def raw1229 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical1229 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1229 = injectiveMoment H node1510 := by
  rfl

def raw1230 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw1230step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical1230 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1230 = injectiveMoment H node1510 := by
  calc
    injectiveMoment H raw1230 = injectiveMoment H raw1230step0 := by
      have heq : raw1230step0 = (fun i j => raw1230 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1230 permutation34 permutation9
    _ = injectiveMoment H node1510 := by rfl

def raw1231 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, 0, 1, -3]]

def raw1231step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, -2, 0, 1], ![3, 1, -1, -3]]

def raw1231step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![-1, 2, 0, -1], ![-3, -1, 1, 3]]

def raw1231step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, -1, -1], ![1, -1, 3, -3]]

theorem canonical1231 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1231 = injectiveMoment H node1035 := by
  calc
    injectiveMoment H raw1231 = injectiveMoment H raw1231step0 := by
      have heq : raw1231step0 = raw1231.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1231).symm
    injectiveMoment H raw1231step0 = injectiveMoment H raw1231step1 := by
      have heq : raw1231step1 = -raw1231step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1231step0).symm
    injectiveMoment H raw1231step1 = injectiveMoment H raw1231step2 := by
      have heq : raw1231step2 = (fun i j => raw1231step1 (permutation15 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1231step1 permutation15 permutation24
    _ = injectiveMoment H node1035 := by rfl

def raw1232 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, 0, -1]]

theorem canonical1232 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1232 = injectiveMoment H node1511 := by
  rfl

def raw1233 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem canonical1233 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1233 = injectiveMoment H node408 := by
  rfl

def raw1234 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![1, 0, -1, 0], ![1, 1, 2, -4]]

def raw1234step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, -2, -1, 2], ![3, 1, 0, -4]]

def raw1234step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, 0, -2, 1]]

theorem canonical1234 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1234 = injectiveMoment H node848 := by
  calc
    injectiveMoment H raw1234 = injectiveMoment H raw1234step0 := by
      have heq : raw1234step0 = raw1234.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1234).symm
    injectiveMoment H raw1234step0 = injectiveMoment H raw1234step1 := by
      have heq : raw1234step1 = (fun i j => raw1234step0 (permutation24 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1234step0 permutation24 permutation23
    _ = injectiveMoment H node848 := by rfl

def raw1235 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 1, 1, -3]]

def raw1235step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 0, 1], ![1, -2, 0, 1], ![3, 1, -1, -3]]

def raw1235step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, 0, -1], ![-1, 2, 0, -1], ![-3, -1, 1, 3]]

def raw1235step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, -1, 3, -3]]

theorem canonical1235 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1235 = injectiveMoment H node1239 := by
  calc
    injectiveMoment H raw1235 = injectiveMoment H raw1235step0 := by
      have heq : raw1235step0 = raw1235.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1235).symm
    injectiveMoment H raw1235step0 = injectiveMoment H raw1235step1 := by
      have heq : raw1235step1 = -raw1235step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1235step0).symm
    injectiveMoment H raw1235step1 = injectiveMoment H raw1235step2 := by
      have heq : raw1235step2 = (fun i j => raw1235step1 (permutation9 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1235step1 permutation9 permutation24
    _ = injectiveMoment H node1239 := by rfl

def raw1236 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 0, -2]]

theorem canonical1236 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1236 = injectiveMoment H node409 := by
  rfl

def raw1237 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![1, 1, 0, -2], ![1, 0, 1, -2]]

def raw1237step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 1, 0, -2]]

theorem canonical1237 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1237 = injectiveMoment H node409 := by
  calc
    injectiveMoment H raw1237 = injectiveMoment H raw1237step0 := by
      have heq : raw1237step0 = (fun i j => raw1237 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1237 permutation10 permutation9
    _ = injectiveMoment H node409 := by rfl

def raw1238 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -2, 1], ![1, 1, 1, -3], ![1, 0, 0, -1]]

def raw1238step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-2, 1, 1, 0], ![1, -2, 1, 0], ![3, 1, -3, -1]]

def raw1238step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![2, -1, -1, 0], ![-1, 2, -1, 0], ![-3, -1, 3, 1]]

def raw1238step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, -1, 2], ![0, 2, -1, -1], ![1, -1, 3, -3]]

theorem canonical1238 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1238 = injectiveMoment H node1239 := by
  calc
    injectiveMoment H raw1238 = injectiveMoment H raw1238step0 := by
      have heq : raw1238step0 = raw1238.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1238).symm
    injectiveMoment H raw1238step0 = injectiveMoment H raw1238step1 := by
      have heq : raw1238step1 = -raw1238step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1238step0).symm
    injectiveMoment H raw1238step1 = injectiveMoment H raw1238step2 := by
      have heq : raw1238step2 = (fun i j => raw1238step1 (permutation9 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1238step1 permutation9 permutation30
    _ = injectiveMoment H node1239 := by rfl

def raw1239 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -2, 1], ![2, 0, 2, -4]]

def raw1239step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, -1, -2, 2], ![3, 0, 1, -4]]

def raw1239step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 1, 2], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

theorem canonical1239 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1239 = injectiveMoment H node830 := by
  calc
    injectiveMoment H raw1239 = injectiveMoment H raw1239step0 := by
      have heq : raw1239step0 = raw1239.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1239).symm
    injectiveMoment H raw1239step0 = injectiveMoment H raw1239step1 := by
      have heq : raw1239step1 = (fun i j => raw1239step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1239step0 permutation22 permutation17
    _ = injectiveMoment H node830 := by rfl

def raw1240 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical1240 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1240 = injectiveMoment H node1512 := by
  rfl

def raw1241 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 0, 0, -1]]

def raw1241step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

theorem canonical1241 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1241 = injectiveMoment H node1512 := by
  calc
    injectiveMoment H raw1241 = injectiveMoment H raw1241step0 := by
      have heq : raw1241step0 = (fun i j => raw1241 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1241 permutation34 permutation9
    _ = injectiveMoment H node1512 := by rfl

def raw1242 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![2, 0, 1, -3]]

def raw1242step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, -1, -1, 1], ![3, 0, 0, -3]]

def raw1242step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![-1, 1, 1, -1], ![-3, 0, 0, 3]]

def raw1242step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, -1, -1]]

theorem canonical1242 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1242 = injectiveMoment H node1028 := by
  calc
    injectiveMoment H raw1242 = injectiveMoment H raw1242step0 := by
      have heq : raw1242step0 = raw1242.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1242).symm
    injectiveMoment H raw1242step0 = injectiveMoment H raw1242step1 := by
      have heq : raw1242step1 = -raw1242step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1242step0).symm
    injectiveMoment H raw1242step1 = injectiveMoment H raw1242step2 := by
      have heq : raw1242step2 = (fun i j => raw1242step1 (permutation16 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1242step1 permutation16 permutation18
    _ = injectiveMoment H node1028 := by rfl

def raw1243 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical1243 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1243 = injectiveMoment H node1513 := by
  rfl

def raw1244 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw1244step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, -2, -2, 3]]

theorem canonical1244 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1244 = injectiveMoment H node2823 := by
  calc
    injectiveMoment H raw1244 = injectiveMoment H raw1244step0 := by
      have heq : raw1244step0 = (fun i j => raw1244 (permutation65 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1244 permutation65 permutation21
    _ = injectiveMoment H node2823 := by rfl

def raw1245 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw1245step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 1, 1, 0], ![1, -1, 0, 0], ![3, 0, -1, -2]]

def raw1245step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, -1, -1, 0], ![-1, 1, 0, 0], ![-3, 0, 1, 2]]

def raw1245step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical1245 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1245 = injectiveMoment H node1032 := by
  calc
    injectiveMoment H raw1245 = injectiveMoment H raw1245step0 := by
      have heq : raw1245step0 = raw1245.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1245).symm
    injectiveMoment H raw1245step0 = injectiveMoment H raw1245step1 := by
      have heq : raw1245step1 = -raw1245step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1245step0).symm
    injectiveMoment H raw1245step1 = injectiveMoment H raw1245step2 := by
      have heq : raw1245step2 = (fun i j => raw1245step1 (permutation15 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1245step1 permutation15 permutation24
    _ = injectiveMoment H node1032 := by rfl

def raw1246 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw1246step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical1246 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1246 = injectiveMoment H node1513 := by
  calc
    injectiveMoment H raw1246 = injectiveMoment H raw1246step0 := by
      have heq : raw1246step0 = (fun i j => raw1246 (permutation49 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1246 permutation49 permutation15
    _ = injectiveMoment H node1513 := by rfl

def raw1247 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, 0, -1], ![1, 0, -1, 0]]

def raw1247step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, 1, 3], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

theorem canonical1247 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1247 = injectiveMoment H node1513 := by
  calc
    injectiveMoment H raw1247 = injectiveMoment H raw1247step0 := by
      have heq : raw1247step0 = (fun i j => raw1247 (permutation55 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1247 permutation55 permutation15
    _ = injectiveMoment H node1513 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
